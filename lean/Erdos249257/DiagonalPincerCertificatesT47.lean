import Erdos249257.DiagonalPincerCertificatesT43
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64

/-!
# The t=47 diagonal-pincer certificate

This generated extension consumes 105 new large-prime Lucas roots
and 1137 recursive Pratt dependencies, reuses 2 earlier certificates,
reconstructs all 146 Euler totients in the t=47 window, and proves the
twenty-third finite diagonal kill without `native_decide`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=47 window -/

private theorem prime_t47_2 : Nat.Prime 2 := by norm_num
private theorem prime_t47_3 : Nat.Prime 3 := by norm_num
private theorem prime_t47_5 : Nat.Prime 5 := by norm_num
private theorem prime_t47_7 : Nat.Prime 7 := by norm_num
private theorem prime_t47_11 : Nat.Prime 11 := by norm_num
private theorem prime_t47_13 : Nat.Prime 13 := by norm_num
private theorem prime_t47_17 : Nat.Prime 17 := by norm_num
private theorem prime_t47_19 : Nat.Prime 19 := by norm_num
private theorem prime_t47_23 : Nat.Prime 23 := by norm_num
private theorem prime_t47_29 : Nat.Prime 29 := by norm_num
private theorem prime_t47_31 : Nat.Prime 31 := by norm_num
private theorem prime_t47_37 : Nat.Prime 37 := by norm_num
private theorem prime_t47_41 : Nat.Prime 41 := by norm_num
private theorem prime_t47_43 : Nat.Prime 43 := by norm_num
private theorem prime_t47_47 : Nat.Prime 47 := by norm_num
private theorem prime_t47_53 : Nat.Prime 53 := by norm_num
private theorem prime_t47_59 : Nat.Prime 59 := by norm_num
private theorem prime_t47_61 : Nat.Prime 61 := by norm_num
private theorem prime_t47_67 : Nat.Prime 67 := by norm_num
private theorem prime_t47_71 : Nat.Prime 71 := by norm_num
private theorem prime_t47_73 : Nat.Prime 73 := by norm_num
private theorem prime_t47_79 : Nat.Prime 79 := by norm_num
private theorem prime_t47_83 : Nat.Prime 83 := by norm_num
private theorem prime_t47_89 : Nat.Prime 89 := by norm_num
private theorem prime_t47_97 : Nat.Prime 97 := by norm_num
private theorem prime_t47_101 : Nat.Prime 101 := by norm_num
private theorem prime_t47_107 : Nat.Prime 107 := by norm_num
private theorem prime_t47_109 : Nat.Prime 109 := by norm_num
private theorem prime_t47_113 : Nat.Prime 113 := by norm_num
private theorem prime_t47_127 : Nat.Prime 127 := by norm_num
private theorem prime_t47_131 : Nat.Prime 131 := by norm_num
private theorem prime_t47_149 : Nat.Prime 149 := by norm_num
private theorem prime_t47_157 : Nat.Prime 157 := by norm_num
private theorem prime_t47_167 : Nat.Prime 167 := by norm_num
private theorem prime_t47_191 : Nat.Prime 191 := by norm_num
private theorem prime_t47_197 : Nat.Prime 197 := by norm_num
private theorem prime_t47_199 : Nat.Prime 199 := by norm_num
private theorem prime_t47_211 : Nat.Prime 211 := by norm_num
private theorem prime_t47_223 : Nat.Prime 223 := by norm_num
private theorem prime_t47_239 : Nat.Prime 239 := by norm_num
private theorem prime_t47_263 : Nat.Prime 263 := by norm_num
private theorem prime_t47_277 : Nat.Prime 277 := by norm_num
private theorem prime_t47_283 : Nat.Prime 283 := by norm_num
private theorem prime_t47_293 : Nat.Prime 293 := by norm_num
private theorem prime_t47_311 : Nat.Prime 311 := by norm_num
private theorem prime_t47_313 : Nat.Prime 313 := by norm_num
private theorem prime_t47_349 : Nat.Prime 349 := by norm_num
private theorem prime_t47_383 : Nat.Prime 383 := by norm_num
private theorem prime_t47_449 : Nat.Prime 449 := by norm_num
private theorem prime_t47_461 : Nat.Prime 461 := by norm_num
private theorem prime_t47_463 : Nat.Prime 463 := by norm_num
private theorem prime_t47_479 : Nat.Prime 479 := by norm_num
private theorem prime_t47_491 : Nat.Prime 491 := by norm_num
private theorem prime_t47_503 : Nat.Prime 503 := by norm_num
private theorem prime_t47_523 : Nat.Prime 523 := by norm_num
private theorem prime_t47_563 : Nat.Prime 563 := by norm_num
private theorem prime_t47_571 : Nat.Prime 571 := by norm_num
private theorem prime_t47_691 : Nat.Prime 691 := by norm_num
private theorem prime_t47_701 : Nat.Prime 701 := by norm_num
private theorem prime_t47_839 : Nat.Prime 839 := by norm_num
private theorem prime_t47_877 : Nat.Prime 877 := by norm_num
private theorem prime_t47_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_t47_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_t47_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_t47_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_t47_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_t47_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_t47_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_t47_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_t47_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_t47_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_t47_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_t47_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_t47_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_t47_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_t47_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_t47_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_t47_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_t47_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_t47_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_t47_2671 : Nat.Prime 2671 := by norm_num
private theorem prime_t47_3313 : Nat.Prime 3313 := by norm_num
private theorem prime_t47_3347 : Nat.Prime 3347 := by norm_num
private theorem prime_t47_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_t47_3631 : Nat.Prime 3631 := by norm_num
private theorem prime_t47_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_t47_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_t47_4091 : Nat.Prime 4091 := by norm_num
private theorem prime_t47_4561 : Nat.Prime 4561 := by norm_num
private theorem prime_t47_5197 : Nat.Prime 5197 := by norm_num
private theorem prime_t47_5483 : Nat.Prime 5483 := by norm_num
private theorem prime_t47_6101 : Nat.Prime 6101 := by norm_num
private theorem prime_t47_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_t47_6869 : Nat.Prime 6869 := by norm_num
private theorem prime_t47_7151 : Nat.Prime 7151 := by norm_num
private theorem prime_t47_7589 : Nat.Prime 7589 := by norm_num
private theorem prime_t47_8263 : Nat.Prime 8263 := by norm_num
private theorem prime_t47_9479 : Nat.Prime 9479 := by norm_num
private theorem prime_t47_9857 : Nat.Prime 9857 := by norm_num
private theorem prime_t47_11117 : Nat.Prime 11117 := by norm_num
private theorem prime_t47_12197 : Nat.Prime 12197 := by norm_num
private theorem prime_t47_12919 : Nat.Prime 12919 := by norm_num
private theorem prime_t47_13477 : Nat.Prime 13477 := by norm_num
private theorem prime_t47_14173 : Nat.Prime 14173 := by norm_num
private theorem prime_t47_14293 : Nat.Prime 14293 := by norm_num
private theorem prime_t47_15583 : Nat.Prime 15583 := by norm_num
private theorem prime_t47_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_t47_15749 : Nat.Prime 15749 := by norm_num
private theorem prime_t47_16381 : Nat.Prime 16381 := by norm_num
private theorem prime_t47_23201 : Nat.Prime 23201 := by norm_num
private theorem prime_t47_24113 : Nat.Prime 24113 := by norm_num
private theorem prime_t47_27061 : Nat.Prime 27061 := by norm_num
private theorem prime_t47_29297 : Nat.Prime 29297 := by norm_num
private theorem prime_t47_30517 : Nat.Prime 30517 := by norm_num
private theorem prime_t47_33287 : Nat.Prime 33287 := by norm_num
private theorem prime_t47_33893 : Nat.Prime 33893 := by norm_num
private theorem prime_t47_34631 : Nat.Prime 34631 := by norm_num
private theorem prime_t47_45119 : Nat.Prime 45119 := by norm_num
private theorem prime_t47_47737 : Nat.Prime 47737 := by norm_num
private theorem prime_t47_50867 : Nat.Prime 50867 := by norm_num
private theorem prime_t47_53299 : Nat.Prime 53299 := by norm_num
private theorem prime_t47_56993 : Nat.Prime 56993 := by norm_num
private theorem prime_t47_57809 : Nat.Prime 57809 := by norm_num
private theorem prime_t47_57839 : Nat.Prime 57839 := by norm_num
private theorem prime_t47_77167 : Nat.Prime 77167 := by norm_num
private theorem prime_t47_79601 : Nat.Prime 79601 := by norm_num
private theorem prime_t47_82609 : Nat.Prime 82609 := by norm_num
private theorem prime_t47_85381 : Nat.Prime 85381 := by norm_num
private theorem prime_t47_87359 : Nat.Prime 87359 := by norm_num
private theorem prime_t47_95089 : Nat.Prime 95089 := by norm_num
private theorem prime_t47_95311 : Nat.Prime 95311 := by norm_num
private theorem prime_t47_98507 : Nat.Prime 98507 := by norm_num
private theorem prime_t47_110437 : Nat.Prime 110437 := by norm_num
private theorem prime_t47_190181 : Nat.Prime 190181 := by norm_num
private theorem prime_t47_193373 : Nat.Prime 193373 := by norm_num
private theorem prime_t47_219979 : Nat.Prime 219979 := by norm_num
private theorem prime_t47_277961 : Nat.Prime 277961 := by norm_num
private theorem prime_t47_305857 : Nat.Prime 305857 := by norm_num
private theorem prime_t47_321707 : Nat.Prime 321707 := by norm_num
private theorem prime_t47_329089 : Nat.Prime 329089 := by norm_num
private theorem prime_t47_330427 : Nat.Prime 330427 := by norm_num
private theorem prime_t47_369791 : Nat.Prime 369791 := by norm_num
private theorem prime_t47_391789 : Nat.Prime 391789 := by norm_num
private theorem prime_t47_400903 : Nat.Prime 400903 := by norm_num
private theorem prime_t47_409021 : Nat.Prime 409021 := by norm_num
private theorem prime_t47_416219 : Nat.Prime 416219 := by norm_num
private theorem prime_t47_467473 : Nat.Prime 467473 := by norm_num
private theorem prime_t47_478627 : Nat.Prime 478627 := by norm_num
private theorem prime_t47_496339 : Nat.Prime 496339 := by norm_num
private theorem prime_t47_542981 : Nat.Prime 542981 := by norm_num
private theorem prime_t47_642013 : Nat.Prime 642013 := by norm_num
private theorem prime_t47_674771 : Nat.Prime 674771 := by norm_num
private theorem prime_t47_739957 : Nat.Prime 739957 := by norm_num
private theorem prime_t47_867827 : Nat.Prime 867827 := by norm_num
private theorem prime_t47_1435163 : Nat.Prime 1435163 := by norm_num
private theorem prime_t47_1573753 : Nat.Prime 1573753 := by norm_num
private theorem prime_t47_1640621 : Nat.Prime 1640621 := by norm_num
private theorem prime_t47_1799417 : Nat.Prime 1799417 := by norm_num
private theorem prime_t47_2726107 : Nat.Prime 2726107 := by norm_num
private theorem prime_t47_2923421 : Nat.Prime 2923421 := by norm_num
private theorem prime_t47_3089899 : Nat.Prime 3089899 := by norm_num
private theorem prime_t47_3290459 : Nat.Prime 3290459 := by norm_num
private theorem prime_t47_3295249 : Nat.Prime 3295249 := by norm_num
private theorem prime_t47_3370517 : Nat.Prime 3370517 := by norm_num
private theorem prime_t47_4808513 : Nat.Prime 4808513 := by norm_num
private theorem prime_t47_4932821 : Nat.Prime 4932821 := by norm_num
private theorem prime_t47_5466983 : Nat.Prime 5466983 := by norm_num
private theorem prime_t47_7551433 : Nat.Prime 7551433 := by norm_num
private theorem prime_t47_7982327 : Nat.Prime 7982327 := by norm_num
private theorem prime_t47_8119187 : Nat.Prime 8119187 := by norm_num
private theorem prime_t47_8724589 : Nat.Prime 8724589 := by norm_num
private theorem prime_t47_10970987 : Nat.Prime 10970987 := by norm_num
private theorem prime_t47_11189369 : Nat.Prime 11189369 := by norm_num
private theorem prime_t47_11958917 : Nat.Prime 11958917 := by norm_num
private theorem prime_t47_11968207 : Nat.Prime 11968207 := by norm_num
private theorem prime_t47_15616691 : Nat.Prime 15616691 := by norm_num
private theorem prime_t47_21845827 : Nat.Prime 21845827 := by norm_num
private theorem prime_t47_22698623 : Nat.Prime 22698623 := by norm_num
private theorem prime_t47_22829977 : Nat.Prime 22829977 := by norm_num
private theorem prime_t47_25372327 : Nat.Prime 25372327 := by norm_num
private theorem prime_t47_27176299 : Nat.Prime 27176299 := by norm_num
private theorem prime_t47_31342247 : Nat.Prime 31342247 := by norm_num
private theorem prime_t47_31715881 : Nat.Prime 31715881 := by norm_num

/-! ## Exact t=47 window totients -/

private theorem phi_t47_442720643463713815201 : Nat.totient 442720643463713815201 = 442720643463713815200 := by
  rw [← show ((([(442720643463713815201, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_442720643463713815201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815202 : Nat.totient 442720643463713815202 = 221360321731856907600 := by
  rw [← show ((([(2, 1), (221360321731856907601, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_lucas_221360321731856907601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815203 : Nat.totient 442720643463713815203 = 295147095642475876800 := by
  rw [← show ((([(3, 1), (147573547821237938401, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_lucas_147573547821237938401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815204 : Nat.totient 442720643463713815204 = 221210853264641133120 := by
  rw [← show ((([(2, 2), (1481, 1), (210808223, 1), (354508927, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_1481, prime_lucas_210808223, prime_lucas_354508927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815205 : Nat.totient 442720643463713815205 = 354176514770971052160 := by
  rw [← show ((([(5, 1), (88544128692742763041, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_lucas_88544128692742763041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815206 : Nat.totient 442720643463713815206 = 147509635500830295008 := by
  rw [← show ((([(2, 1), (3, 1), (2309, 1), (31956160203819389, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_2309, prime_lucas_31956160203819389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815207 : Nat.totient 442720643463713815207 = 379439337505962827520 := by
  rw [← show ((([(7, 1), (11117, 1), (277961, 1), (20467286173, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_7, prime_t47_11117, prime_t47_277961, prime_lucas_20467286173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815208 : Nat.totient 442720643463713815208 = 220967007075554247360 := by
  rw [← show ((([(2, 3), (563, 1), (1640621, 1), (59913283987, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_563, prime_t47_1640621, prime_lucas_59913283987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815209 : Nat.totient 442720643463713815209 = 293335609289825203200 := by
  rw [← show ((([(3, 2), (277, 1), (877, 1), (1321, 1), (1559, 1), (98323871, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_277, prime_t47_877, prime_t47_1321, prime_t47_1559, prime_lucas_98323871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815210 : Nat.totient 442720643463713815210 = 177055959691269657808 := by
  rw [← show ((([(2, 1), (5, 1), (5483, 1), (8074423553961587, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_5483, prime_lucas_8074423553961587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815211 : Nat.totient 442720643463713815211 = 390797268789253248000 := by
  rw [← show ((([(11, 1), (53, 1), (97, 1), (34631, 1), (226060379131, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_11, prime_t47_53, prime_t47_97, prime_t47_34631, prime_lucas_226060379131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815212 : Nat.totient 442720643463713815212 = 147102066837783502848 := by
  rw [← show ((([(2, 2), (3, 1), (313, 1), (117870245863608577, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_313, prime_lucas_117870245863608577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815213 : Nat.totient 442720643463713815213 = 402504070515494086656 := by
  rw [← show ((([(13, 1), (67, 1), (6529, 1), (77851135148107, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_13, prime_t47_67, prime_t47_6529, prime_lucas_77851135148107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815214 : Nat.totient 442720643463713815214 = 189737418627305920800 := by
  rw [← show ((([(2, 1), (7, 1), (31622903104550986801, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_7, prime_lucas_31622903104550986801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815215 : Nat.totient 442720643463713815215 = 236117676396626621600 := by
  rw [← show ((([(3, 1), (5, 1), (2406944171, 1), (12262315811, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_5, prime_lucas_2406944171, prime_lucas_12262315811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815216 : Nat.totient 442720643463713815216 = 221177811505025406720 := by
  rw [← show ((([(2, 4), (1213, 1), (10970987, 1), (2079233621, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_1213, prime_t47_10970987, prime_lucas_2079233621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815217 : Nat.totient 442720643463713815217 = 416676580732453386240 := by
  rw [← show ((([(17, 1), (409021, 1), (642013, 1), (99172537, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_17, prime_t47_409021, prime_t47_642013, prime_lucas_99172537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815218 : Nat.totient 442720643463713815218 = 147568500070661248128 := by
  rw [← show ((([(2, 1), (3, 2), (29297, 1), (21845827, 1), (38429579, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_29297, prime_t47_21845827, prime_lucas_38429579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815219 : Nat.totient 442720643463713815219 = 419414359010182335360 := by
  rw [← show ((([(19, 2), (85381, 1), (1799417, 1), (7982327, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_19, prime_t47_85381, prime_t47_1799417, prime_t47_7982327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815220 : Nat.totient 442720643463713815220 = 176892031415458187136 := by
  rw [← show ((([(2, 2), (5, 1), (1013, 1), (8263, 1), (2644554851219, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_1013, prime_t47_8263, prime_lucas_2644554851219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815221 : Nat.totient 442720643463713815221 = 252982579123468842048 := by
  rw [← show ((([(3, 1), (7, 1), (391789, 1), (53809411195909, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_7, prime_t47_391789, prime_lucas_53809411195909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815222 : Nat.totient 442720643463713815222 = 201235053096931260000 := by
  rw [← show ((([(2, 1), (11, 1), (190181, 1), (369791, 1), (286143331, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_11, prime_t47_190181, prime_t47_369791, prime_lucas_286143331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815223 : Nat.totient 442720643463713815223 = 416274683597794560000 := by
  rw [← show ((([(23, 1), (101, 1), (197, 1), (479, 1), (79601, 1), (25372327, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_23, prime_t47_101, prime_t47_197, prime_t47_479, prime_t47_79601, prime_t47_25372327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815224 : Nat.totient 442720643463713815224 = 147572876968346488032 := by
  rw [← show ((([(2, 3), (3, 1), (219979, 1), (83856611211319, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_219979, prime_lucas_83856611211319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815225 : Nat.totient 442720643463713815225 = 348584542048612224000 := by
  rw [← show ((([(5, 2), (83, 1), (293, 1), (2671, 1), (272627815441, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_83, prime_t47_293, prime_t47_2671, prime_lucas_272627815441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815226 : Nat.totient 442720643463713815226 = 200922841177393890240 := by
  rw [← show ((([(2, 1), (13, 1), (61, 1), (3347, 1), (83400926968103, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_13, prime_t47_61, prime_t47_3347, prime_lucas_83400926968103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815227 : Nat.totient 442720643463713815227 = 295146696771831759120 := by
  rw [← show ((([(3, 4), (739957, 1), (7386492669631, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_739957, prime_lucas_7386492669631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815228 : Nat.totient 442720643463713815228 = 189299365276733712000 := by
  rw [← show ((([(2, 2), (7, 2), (461, 1), (7151, 1), (685182083413, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_7, prime_t47_461, prime_t47_7151, prime_lucas_685182083413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815229 : Nat.totient 442720643463713815229 = 427452731724446023680 := by
  rw [← show ((([(29, 1), (305857, 1), (1573753, 1), (31715881, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_29, prime_t47_305857, prime_t47_1573753, prime_t47_31715881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815230 : Nat.totient 442720643463713815230 = 116010135299952198144 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (59, 1), (2437, 1), (1435163, 1), (71515429, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_5, prime_t47_59, prime_t47_2437, prime_t47_1435163, prime_lucas_71515429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815231 : Nat.totient 442720643463713815231 = 428327555882182124160 := by
  rw [← show ((([(31, 1), (3833, 1), (3725883401897897, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_31, prime_t47_3833, prime_lucas_3725883401897897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815232 : Nat.totient 442720643463713815232 = 221360321198716160256 := by
  rw [← show ((([(2, 6), (426098039, 1), (16234550317, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_lucas_426098039, prime_lucas_16234550317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815233 : Nat.totient 442720643463713815233 = 268315454656751176080 := by
  rw [← show ((([(3, 1), (11, 1), (3089899, 1), (4341817345699, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_11, prime_t47_3089899, prime_lucas_4341817345699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815234 : Nat.totient 442720643463713815234 = 208338817580548897600 := by
  rw [← show ((([(2, 1), (17, 1), (674771, 1), (19297206601931, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_17, prime_t47_674771, prime_lucas_19297206601931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815235 : Nat.totient 442720643463713815235 = 300723090644283310080 := by
  rw [← show ((([(5, 1), (7, 1), (127, 1), (691, 1), (9857, 1), (14622957029, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_7, prime_t47_127, prime_t47_691, prime_t47_9857, prime_lucas_14622957029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815236 : Nat.totient 442720643463713815236 = 147469841884610206704 := by
  rw [← show ((([(2, 2), (3, 2), (1423, 1), (8642161385642887, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_1423, prime_lucas_8642161385642887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815237 : Nat.totient 442720643463713815237 = 424854464219898537600 := by
  rw [← show ((([(37, 2), (73, 1), (4429997332956901, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_37, prime_t47_73, prime_lucas_4429997332956901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815238 : Nat.totient 442720643463713815238 = 209709778482811807200 := by
  rw [← show ((([(2, 1), (19, 1), (11650543249045100401, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_19, prime_lucas_11650543249045100401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815239 : Nat.totient 442720643463713815239 = 272317942014187345920 := by
  rw [← show ((([(3, 1), (13, 1), (2221, 1), (95089, 1), (53750972629, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_13, prime_t47_2221, prime_t47_95089, prime_lucas_53750972629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815240 : Nat.totient 442720643463713815240 = 176993099804945203200 := by
  rw [← show ((([(2, 3), (5, 1), (1861, 1), (5947348783768321, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_1861, prime_lucas_5947348783768321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815241 : Nat.totient 442720643463713815241 = 431685532197694720000 := by
  rw [← show ((([(41, 1), (2351, 1), (12197, 1), (24113, 1), (15616691, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_41, prime_t47_2351, prime_t47_12197, prime_t47_24113, prime_t47_15616691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815242 : Nat.totient 442720643463713815242 = 126470394460502867520 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (6869, 1), (45119, 1), (34011634291, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_7, prime_t47_6869, prime_t47_45119, prime_lucas_34011634291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815243 : Nat.totient 442720643463713815243 = 430846049821673472000 := by
  rw [← show ((([(43, 1), (449, 1), (701, 1), (2923421, 1), (11189369, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_43, prime_t47_449, prime_t47_701, prime_t47_2923421, prime_t47_11189369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815244 : Nat.totient 442720643463713815244 = 198311825884788608000 := by
  rw [← show ((([(2, 2), (11, 1), (107, 1), (191, 1), (542981, 1), (906724433, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_11, prime_t47_107, prime_t47_191, prime_t47_542981, prime_lucas_906724433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815245 : Nat.totient 442720643463713815245 = 236110709952255815808 := by
  rw [← show ((([(3, 2), (5, 1), (33893, 1), (290273405169677, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_5, prime_t47_33893, prime_lucas_290273405169677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815246 : Nat.totient 442720643463713815246 = 211735915883759601664 := by
  rw [← show ((([(2, 1), (23, 1), (4808513, 1), (2001525588977, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_23, prime_t47_4808513, prime_lucas_2001525588977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815247 : Nat.totient 442720643463713815247 = 427054907645433291840 := by
  rw [← show ((([(47, 1), (89, 1), (311, 1), (340315335048319, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_47, prime_t47_89, prime_t47_311, prime_lucas_340315335048319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815248 : Nat.totient 442720643463713815248 = 147572740758322540032 := by
  rw [← show ((([(2, 4), (3, 1), (193373, 1), (5466983, 1), (8724589, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_193373, prime_t47_5466983, prime_t47_8724589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815249 : Nat.totient 442720643463713815249 = 375991829471440207872 := by
  rw [← show ((([(7, 1), (113, 1), (3313, 1), (33287, 1), (5075247169, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_7, prime_t47_113, prime_t47_3313, prime_t47_33287, prime_lucas_5075247169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815250 : Nat.totient 442720643463713815250 = 177072158053050624000 := by
  rw [← show ((([(2, 1), (5, 3), (14293, 1), (47737, 1), (2595441521, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_14293, prime_t47_47737, prime_lucas_2595441521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815251 : Nat.totient 442720643463713815251 = 277254363154421142144 := by
  rw [← show ((([(3, 1), (17, 1), (523, 1), (16598082085393987, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_17, prime_t47_523, prime_lucas_16598082085393987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815252 : Nat.totient 442720643463713815252 = 204332604675560222400 := by
  rw [← show ((([(2, 2), (13, 1), (8513858528148342601, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_13, prime_lucas_8513858528148342601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815253 : Nat.totient 442720643463713815253 = 442720642024230298080 := by
  rw [← show ((([(307620941, 1), (1439175896233, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_307620941, prime_lucas_1439175896233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815254 : Nat.totient 442720643463713815254 = 147573547821237938400 := by
  rw [← show ((([(2, 1), (3, 3), (8198530434513218801, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_lucas_8198530434513218801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815255 : Nat.totient 442720643463713815255 = 320840916046944533280 := by
  rw [← show ((([(5, 1), (11, 1), (283, 1), (28443343621183027, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_11, prime_t47_283, prime_lucas_28443343621183027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815256 : Nat.totient 442720643463713815256 = 185213974208982630912 := by
  rw [← show ((([(2, 3), (7, 1), (79, 1), (109, 1), (463, 1), (87359, 1), (22698623, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_7, prime_t47_79, prime_t47_109, prime_t47_463, prime_t47_87359, prime_t47_22698623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815257 : Nat.totient 442720643463713815257 = 279612340518984657552 := by
  rw [← show ((([(3, 1), (19, 1), (400903, 1), (19373835647767, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_19, prime_t47_400903, prime_lucas_19373835647767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815258 : Nat.totient 442720643463713815258 = 213517875938458996800 := by
  rw [← show ((([(2, 1), (29, 1), (1021, 1), (7476116104287781, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_29, prime_t47_1021, prime_lucas_7476116104287781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815259 : Nat.totient 442720643463713815259 = 442657812597153760096 := by
  rw [← show ((([(7589, 1), (98507, 1), (592213259933, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_7589, prime_t47_98507, prime_lucas_592213259933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815260 : Nat.totient 442720643463713815260 = 117720314826108403968 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (349, 1), (478627, 1), (44172898927, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_5, prime_t47_349, prime_t47_478627, prime_lucas_44172898927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815261 : Nat.totient 442720643463713815261 = 442720642933169178172 := by
  rw [← show ((([(835781087, 1), (529708856003, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_835781087, prime_lucas_529708856003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815262 : Nat.totient 442720643463713815262 = 213725734505920072800 := by
  rw [← show ((([(2, 1), (31, 1), (491, 1), (3709, 1), (3921026324879, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_31, prime_t47_491, prime_t47_3709, prime_lucas_3921026324879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815263 : Nat.totient 442720643463713815263 = 252983224836407894400 := by
  rw [← show ((([(3, 2), (7, 1), (7027311801011330401, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_7, prime_lucas_7027311801011330401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815264 : Nat.totient 442720643463713815264 = 216787268202968586240 := by
  rw [← show ((([(2, 5), (53, 1), (571, 1), (13477, 1), (33921464077, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_53, prime_t47_571, prime_t47_13477, prime_lucas_33921464077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815265 : Nat.totient 442720643463713815265 = 326932068267547471872 := by
  rw [← show ((([(5, 1), (13, 1), (3295249, 1), (2066941473169, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_13, prime_t47_3295249, prime_lucas_2066941473169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815266 : Nat.totient 442720643463713815266 = 134157770746579944000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (6707888537328997201, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_11, prime_lucas_6707888537328997201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815267 : Nat.totient 442720643463713815267 = 440495862356832121224 := by
  rw [← show ((([(199, 1), (8119187, 1), (274008573959, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_199, prime_t47_8119187, prime_lucas_274008573959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815268 : Nat.totient 442720643463713815268 = 208189685003874577920 := by
  rw [← show ((([(2, 2), (17, 1), (1531, 1), (15583, 1), (272894384437, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_17, prime_t47_1531, prime_t47_15583, prime_lucas_272894384437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815269 : Nat.totient 442720643463713815269 = 278338294624175016000 := by
  rw [← show ((([(3, 1), (23, 1), (71, 1), (4932821, 1), (18320063611, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_23, prime_t47_71, prime_t47_4932821, prime_lucas_18320063611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815270 : Nat.totient 442720643463713815270 = 150579641167464765312 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (239, 1), (263, 1), (330427, 1), (304510699, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_7, prime_t47_239, prime_t47_263, prime_t47_330427, prime_lucas_304510699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815271 : Nat.totient 442720643463713815271 = 441840348857799048952 := by
  rw [← show ((([(503, 1), (3290459, 1), (267488616323, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_503, prime_t47_3290459, prime_lucas_267488616323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815272 : Nat.totient 442720643463713815272 = 147571999484235501600 := by
  rw [← show ((([(2, 3), (3, 2), (95311, 1), (64514041672891, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_95311, prime_lucas_64514041672891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_442720643463713815273 : Nat.totient 442720643463713815273 = 442692337269242551680 := by
  rw [← show ((([(15661, 1), (11958917, 1), (2363841929, 1)] : List FactorBlock).map factorBlockValue).prod) = 442720643463713815273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_15661, prime_t47_11958917, prime_lucas_2363841929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630401 : Nat.totient 885441286927427630401 = 858182005475127675648 := by
  rw [← show ((([(59, 1), (73, 1), (2617, 1), (78556327905779, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_59, prime_t47_73, prime_t47_2617, prime_lucas_78556327905779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630402 : Nat.totient 885441286927427630402 = 442720643463713815200 := by
  rw [← show ((([(2, 1), (442720643463713815201, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_lucas_442720643463713815201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630403 : Nat.totient 885441286927427630403 = 584878648245640269408 := by
  rw [← show ((([(3, 1), (109, 1), (2707771519655741989, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_109, prime_lucas_2707771519655741989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630404 : Nat.totient 885441286927427630404 = 442720643463713815200 := by
  rw [← show ((([(2, 2), (221360321731856907601, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_lucas_221360321731856907601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630405 : Nat.totient 885441286927427630405 = 700371055792493809152 := by
  rw [← show ((([(5, 1), (89, 1), (30517, 1), (65201549987237, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_89, prime_t47_30517, prime_lucas_65201549987237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630406 : Nat.totient 885441286927427630406 = 295147095642475876800 := by
  rw [← show ((([(2, 1), (3, 1), (147573547821237938401, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_lucas_147573547821237938401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630407 : Nat.totient 885441286927427630407 = 758949611094905188896 := by
  rw [← show ((([(7, 2), (11968207, 1), (1509852757849, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_7, prime_t47_11968207, prime_lucas_1509852757849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630408 : Nat.totient 885441286927427630408 = 442421706529282266240 := by
  rw [← show ((([(2, 3), (1481, 1), (210808223, 1), (354508927, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_1481, prime_lucas_210808223, prime_lucas_354508927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630409 : Nat.totient 885441286927427630409 = 588711412726609420512 := by
  rw [← show ((([(3, 2), (383, 1), (14173, 1), (18124110366539, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_383, prime_t47_14173, prime_lucas_18124110366539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630410 : Nat.totient 885441286927427630410 = 354176514770971052160 := by
  rw [← show ((([(2, 1), (5, 1), (88544128692742763041, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_lucas_88544128692742763041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630411 : Nat.totient 885441286927427630411 = 804946624479479664000 := by
  rw [← show ((([(11, 1), (80494662447947966401, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_11, prime_lucas_80494662447947966401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630412 : Nat.totient 885441286927427630412 = 295019271001660590016 := by
  rw [← show ((([(2, 2), (3, 1), (2309, 1), (31956160203819389, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_2309, prime_lucas_31956160203819389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630413 : Nat.totient 885441286927427630413 = 816920318140925140224 := by
  rw [← show ((([(13, 1), (1993, 1), (34175046776310457, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_13, prime_t47_1993, prime_lucas_34175046776310457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630414 : Nat.totient 885441286927427630414 = 379439337505962827520 := by
  rw [← show ((([(2, 1), (7, 1), (11117, 1), (277961, 1), (20467286173, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_7, prime_t47_11117, prime_t47_277961, prime_lucas_20467286173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630415 : Nat.totient 885441286927427630415 = 472119920284615498400 := by
  rw [← show ((([(3, 1), (5, 1), (4091, 1), (14429092918233971, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_5, prime_t47_4091, prime_lucas_14429092918233971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630416 : Nat.totient 885441286927427630416 = 441934014151108494720 := by
  rw [← show ((([(2, 4), (563, 1), (1640621, 1), (59913283987, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_563, prime_t47_1640621, prime_lucas_59913283987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630417 : Nat.totient 885441286927427630417 = 827503646646681241600 := by
  rw [← show ((([(17, 1), (149, 1), (3371, 1), (57839, 1), (1792854521, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_17, prime_t47_149, prime_t47_3371, prime_t47_57839, prime_lucas_1792854521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630418 : Nat.totient 885441286927427630418 = 293335609289825203200 := by
  rw [← show ((([(2, 1), (3, 2), (277, 1), (877, 1), (1321, 1), (1559, 1), (98323871, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_277, prime_t47_877, prime_t47_1321, prime_t47_1559, prime_lucas_98323871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630419 : Nat.totient 885441286927427630419 = 838839113324430602472 := by
  rw [← show ((([(19, 1), (1444231339, 1), (32267803459, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_19, prime_lucas_1444231339, prime_lucas_32267803459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630420 : Nat.totient 885441286927427630420 = 354111919382539315616 := by
  rw [← show ((([(2, 2), (5, 1), (5483, 1), (8074423553961587, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_5483, prime_lucas_8074423553961587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630421 : Nat.totient 885441286927427630421 = 505947726096498354240 := by
  rw [← show ((([(3, 1), (7, 1), (27061, 1), (31342247, 1), (49712603, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_7, prime_t47_27061, prime_t47_31342247, prime_lucas_49712603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630422 : Nat.totient 885441286927427630422 = 390797268789253248000 := by
  rw [← show ((([(2, 1), (11, 1), (53, 1), (97, 1), (34631, 1), (226060379131, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_11, prime_t47_53, prime_t47_97, prime_t47_34631, prime_lucas_226060379131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630423 : Nat.totient 885441286927427630423 = 843144081604672788864 := by
  rw [← show ((([(23, 1), (223, 1), (467473, 1), (369292542319, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_23, prime_t47_223, prime_t47_467473, prime_lucas_369292542319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630424 : Nat.totient 885441286927427630424 = 294204133675567005696 := by
  rw [← show ((([(2, 3), (3, 1), (313, 1), (117870245863608577, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_313, prime_lucas_117870245863608577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630425 : Nat.totient 885441286927427630425 = 708339739367087064720 := by
  rw [← show ((([(5, 2), (53299, 1), (664508742698683, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_53299, prime_lucas_664508742698683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630426 : Nat.totient 885441286927427630426 = 402504070515494086656 := by
  rw [← show ((([(2, 1), (13, 1), (67, 1), (6529, 1), (77851135148107, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_13, prime_t47_67, prime_t47_6529, prime_lucas_77851135148107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630427 : Nat.totient 885441286927427630427 = 585618015274600089600 := by
  rw [← show ((([(3, 3), (131, 1), (5197, 1), (16381, 1), (50867, 1), (57809, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_131, prime_t47_5197, prime_t47_16381, prime_t47_50867, prime_t47_57809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630428 : Nat.totient 885441286927427630428 = 379474837254611841600 := by
  rw [← show ((([(2, 2), (7, 1), (31622903104550986801, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_7, prime_lucas_31622903104550986801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630429 : Nat.totient 885441286927427630429 = 854908828757516332800 := by
  rw [← show ((([(29, 1), (30532458169911297601, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_29, prime_lucas_30532458169911297601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630430 : Nat.totient 885441286927427630430 = 236117676396626621600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (2406944171, 1), (12262315811, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_5, prime_lucas_2406944171, prime_lucas_12262315811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630431 : Nat.totient 885441286927427630431 = 856878664768478352000 := by
  rw [← show ((([(31, 1), (28562622158949278401, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_31, prime_lucas_28562622158949278401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630432 : Nat.totient 885441286927427630432 = 442355623010050813440 := by
  rw [← show ((([(2, 5), (1213, 1), (10970987, 1), (2079233621, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_1213, prime_t47_10970987, prime_lucas_2079233621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630433 : Nat.totient 885441286927427630433 = 529813825738629120000 := by
  rw [← show ((([(3, 1), (11, 1), (79, 1), (23201, 1), (329089, 1), (44483471, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_11, prime_t47_79, prime_t47_23201, prime_t47_329089, prime_lucas_44483471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630434 : Nat.totient 885441286927427630434 = 416676580732453386240 := by
  rw [← show ((([(2, 1), (17, 1), (409021, 1), (642013, 1), (99172537, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_17, prime_t47_409021, prime_t47_642013, prime_lucas_99172537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630435 : Nat.totient 885441286927427630435 = 607046012463773038464 := by
  rw [← show ((([(5, 1), (7, 1), (9479, 1), (12919, 1), (416219, 1), (496339, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_7, prime_t47_9479, prime_t47_12919, prime_t47_416219, prime_t47_496339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630436 : Nat.totient 885441286927427630436 = 295137000141322496256 := by
  rw [← show ((([(2, 2), (3, 2), (29297, 1), (21845827, 1), (38429579, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_29297, prime_t47_21845827, prime_lucas_38429579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630437 : Nat.totient 885441286927427630437 = 860842085678211942144 := by
  rw [← show ((([(37, 1), (1289, 1), (18565434905068409, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_37, prime_t47_1289, prime_lucas_18565434905068409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630438 : Nat.totient 885441286927427630438 = 419414359010182335360 := by
  rw [← show ((([(2, 1), (19, 2), (85381, 1), (1799417, 1), (7982327, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_19, prime_t47_85381, prime_t47_1799417, prime_t47_7982327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630439 : Nat.totient 885441286927427630439 = 544729821343682135040 := by
  rw [← show ((([(3, 1), (13, 1), (3631, 1), (77167, 1), (81028406113, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_13, prime_t47_3631, prime_t47_77167, prime_lucas_81028406113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630440 : Nat.totient 885441286927427630440 = 353784062830916374272 := by
  rw [← show ((([(2, 3), (5, 1), (1013, 1), (8263, 1), (2644554851219, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_1013, prime_t47_8263, prime_lucas_2644554851219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630441 : Nat.totient 885441286927427630441 = 858342644642175189120 := by
  rw [← show ((([(41, 1), (157, 1), (2726107, 1), (50458386799, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_41, prime_t47_157, prime_t47_2726107, prime_lucas_50458386799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630442 : Nat.totient 885441286927427630442 = 252982579123468842048 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (391789, 1), (53809411195909, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_7, prime_t47_391789, prime_lucas_53809411195909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630443 : Nat.totient 885441286927427630443 = 864215970708121659936 := by
  rw [← show ((([(43, 1), (1367, 1), (867827, 1), (17357598589, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_43, prime_t47_1367, prime_t47_867827, prime_lucas_17357598589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630444 : Nat.totient 885441286927427630444 = 402470106193862520000 := by
  rw [← show ((([(2, 2), (11, 1), (190181, 1), (369791, 1), (286143331, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_11, prime_t47_190181, prime_t47_369791, prime_lucas_286143331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630445 : Nat.totient 885441286927427630445 = 469407596423003546208 := by
  rw [← show ((([(3, 2), (5, 1), (167, 1), (117823191873243863, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_5, prime_t47_167, prime_lucas_117823191873243863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630446 : Nat.totient 885441286927427630446 = 416274683597794560000 := by
  rw [← show ((([(2, 1), (23, 1), (101, 1), (197, 1), (479, 1), (79601, 1), (25372327, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_23, prime_t47_101, prime_t47_197, prime_t47_479, prime_t47_79601, prime_t47_25372327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630447 : Nat.totient 885441286927427630447 = 866412107954569382400 := by
  rw [← show ((([(47, 1), (4561, 1), (4130492505504241, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_47, prime_t47_4561, prime_lucas_4130492505504241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630448 : Nat.totient 885441286927427630448 = 295145753936692976064 := by
  rw [← show ((([(2, 4), (3, 1), (219979, 1), (83856611211319, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_219979, prime_lucas_83856611211319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630449 : Nat.totient 885441286927427630449 = 758949674509223683236 := by
  rw [← show ((([(7, 1), (126491612418203947207, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_7, prime_lucas_126491612418203947207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630450 : Nat.totient 885441286927427630450 = 348584542048612224000 := by
  rw [← show ((([(2, 1), (5, 2), (83, 1), (293, 1), (2671, 1), (272627815441, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_83, prime_t47_293, prime_t47_2671, prime_lucas_272627815441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630451 : Nat.totient 885441286927427630451 = 555571003562307532800 := by
  rw [← show ((([(3, 1), (17, 1), (17361593861322110401, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_17, prime_lucas_17361593861322110401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630452 : Nat.totient 885441286927427630452 = 401845682354787780480 := by
  rw [← show ((([(2, 2), (13, 1), (61, 1), (3347, 1), (83400926968103, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_13, prime_t47_61, prime_t47_3347, prime_lucas_83400926968103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630453 : Nat.totient 885441286927427630453 = 885441286927427630452 := by
  rw [← show ((([(885441286927427630453, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_885441286927427630453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630454 : Nat.totient 885441286927427630454 = 295146696771831759120 := by
  rw [← show ((([(2, 1), (3, 4), (739957, 1), (7386492669631, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_739957, prime_lucas_7386492669631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630455 : Nat.totient 885441286927427630455 = 643383873671220295680 := by
  rw [← show ((([(5, 1), (11, 2), (1123, 1), (1303240709915777, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_11, prime_t47_1123, prime_lucas_1303240709915777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630456 : Nat.totient 885441286927427630456 = 378598730553467424000 := by
  rw [← show ((([(2, 3), (7, 2), (461, 1), (7151, 1), (685182083413, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_7, prime_t47_461, prime_t47_7151, prime_lucas_685182083413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630457 : Nat.totient 885441286927427630457 = 559226075954164819200 := by
  rw [← show ((([(3, 1), (19, 1), (15534057665393467201, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_19, prime_lucas_15534057665393467201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630458 : Nat.totient 885441286927427630458 = 427452731724446023680 := by
  rw [← show ((([(2, 1), (29, 1), (305857, 1), (1573753, 1), (31715881, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_29, prime_t47_305857, prime_t47_1573753, prime_t47_31715881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630459 : Nat.totient 885441286927427630459 = 885433248026487239040 := by
  rw [← show ((([(110437, 1), (60730927, 1), (132018641, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_110437, prime_lucas_60730927, prime_lucas_132018641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630460 : Nat.totient 885441286927427630460 = 232020270599904396288 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (59, 1), (2437, 1), (1435163, 1), (71515429, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_5, prime_t47_59, prime_t47_2437, prime_t47_1435163, prime_lucas_71515429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630461 : Nat.totient 885441286927427630461 = 885430450590001731072 := by
  rw [← show ((([(82609, 1), (7551433, 1), (1419394213, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_82609, prime_t47_7551433, prime_lucas_1419394213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630462 : Nat.totient 885441286927427630462 = 428327555882182124160 := by
  rw [← show ((([(2, 1), (31, 1), (3833, 1), (3725883401897897, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_31, prime_t47_3833, prime_lucas_3725883401897897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630463 : Nat.totient 885441286927427630463 = 505966449672815788800 := by
  rw [← show ((([(3, 2), (7, 1), (14054623602022660801, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_7, prime_lucas_14054623602022660801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630464 : Nat.totient 885441286927427630464 = 442720642397432320512 := by
  rw [← show ((([(2, 7), (426098039, 1), (16234550317, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_lucas_426098039, prime_lucas_16234550317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630465 : Nat.totient 885441286927427630465 = 649989586379167856640 := by
  rw [← show ((([(5, 1), (13, 1), (211, 1), (839, 1), (3370517, 1), (22829977, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_5, prime_t47_13, prime_t47_211, prime_t47_839, prime_t47_3370517, prime_t47_22829977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630466 : Nat.totient 885441286927427630466 = 268315454656751176080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (3089899, 1), (4341817345699, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_11, prime_t47_3089899, prime_lucas_4341817345699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630467 : Nat.totient 885441286927427630467 = 872914852682189425920 := by
  rw [← show ((([(71, 1), (15749, 1), (791860057224673, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_71, prime_t47_15749, prime_lucas_791860057224673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630468 : Nat.totient 885441286927427630468 = 416677635161097795200 := by
  rw [← show ((([(2, 2), (17, 1), (674771, 1), (19297206601931, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_17, prime_t47_674771, prime_lucas_19297206601931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630469 : Nat.totient 885441286927427630469 = 564536679449844200000 := by
  rw [← show ((([(3, 1), (23, 1), (6101, 1), (2103340832525501, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_3, prime_t47_23, prime_t47_6101, prime_lucas_2103340832525501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630470 : Nat.totient 885441286927427630470 = 300723090644283310080 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (127, 1), (691, 1), (9857, 1), (14622957029, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_5, prime_t47_7, prime_t47_127, prime_t47_691, prime_t47_9857, prime_lucas_14622957029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630471 : Nat.totient 885441286927427630471 = 885441261959550456744 := by
  rw [← show ((([(35463269, 1), (24967841710459, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_35463269, prime_lucas_24967841710459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630472 : Nat.totient 885441286927427630472 = 294939683769220413408 := by
  rw [← show ((([(2, 3), (3, 2), (1423, 1), (8642161385642887, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_2, prime_t47_3, prime_t47_1423, prime_lucas_8642161385642887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t47_885441286927427630473 : Nat.totient 885441286927427630473 = 884924697696454711296 := by
  rw [← show ((([(1777, 1), (56993, 1), (321707, 1), (27176299, 1)] : List FactorBlock).map factorBlockValue).prod) = 885441286927427630473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t47_1777, prime_t47_56993, prime_t47_321707, prime_t47_27176299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twenty-third finite diagonal certificate -/

theorem certifiedKill_diagonal_t47 :
    certifiedKill (periodLcm 47) (periodLcm 47) 73 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t47_442720643463713815201, phi_t47_442720643463713815202, phi_t47_442720643463713815203, phi_t47_442720643463713815204, phi_t47_442720643463713815205, phi_t47_442720643463713815206, phi_t47_442720643463713815207, phi_t47_442720643463713815208, phi_t47_442720643463713815209, phi_t47_442720643463713815210, phi_t47_442720643463713815211, phi_t47_442720643463713815212, phi_t47_442720643463713815213, phi_t47_442720643463713815214, phi_t47_442720643463713815215, phi_t47_442720643463713815216, phi_t47_442720643463713815217, phi_t47_442720643463713815218, phi_t47_442720643463713815219, phi_t47_442720643463713815220, phi_t47_442720643463713815221, phi_t47_442720643463713815222, phi_t47_442720643463713815223, phi_t47_442720643463713815224, phi_t47_442720643463713815225, phi_t47_442720643463713815226, phi_t47_442720643463713815227, phi_t47_442720643463713815228, phi_t47_442720643463713815229, phi_t47_442720643463713815230, phi_t47_442720643463713815231, phi_t47_442720643463713815232, phi_t47_442720643463713815233, phi_t47_442720643463713815234, phi_t47_442720643463713815235, phi_t47_442720643463713815236, phi_t47_442720643463713815237, phi_t47_442720643463713815238, phi_t47_442720643463713815239, phi_t47_442720643463713815240, phi_t47_442720643463713815241, phi_t47_442720643463713815242, phi_t47_442720643463713815243, phi_t47_442720643463713815244, phi_t47_442720643463713815245, phi_t47_442720643463713815246, phi_t47_442720643463713815247, phi_t47_442720643463713815248, phi_t47_442720643463713815249, phi_t47_442720643463713815250, phi_t47_442720643463713815251, phi_t47_442720643463713815252, phi_t47_442720643463713815253, phi_t47_442720643463713815254, phi_t47_442720643463713815255, phi_t47_442720643463713815256, phi_t47_442720643463713815257, phi_t47_442720643463713815258, phi_t47_442720643463713815259, phi_t47_442720643463713815260, phi_t47_442720643463713815261, phi_t47_442720643463713815262, phi_t47_442720643463713815263, phi_t47_442720643463713815264, phi_t47_442720643463713815265, phi_t47_442720643463713815266, phi_t47_442720643463713815267, phi_t47_442720643463713815268, phi_t47_442720643463713815269, phi_t47_442720643463713815270, phi_t47_442720643463713815271, phi_t47_442720643463713815272, phi_t47_442720643463713815273, phi_t47_885441286927427630401, phi_t47_885441286927427630402, phi_t47_885441286927427630403, phi_t47_885441286927427630404, phi_t47_885441286927427630405, phi_t47_885441286927427630406, phi_t47_885441286927427630407, phi_t47_885441286927427630408, phi_t47_885441286927427630409, phi_t47_885441286927427630410, phi_t47_885441286927427630411, phi_t47_885441286927427630412, phi_t47_885441286927427630413, phi_t47_885441286927427630414, phi_t47_885441286927427630415, phi_t47_885441286927427630416, phi_t47_885441286927427630417, phi_t47_885441286927427630418, phi_t47_885441286927427630419, phi_t47_885441286927427630420, phi_t47_885441286927427630421, phi_t47_885441286927427630422, phi_t47_885441286927427630423, phi_t47_885441286927427630424, phi_t47_885441286927427630425, phi_t47_885441286927427630426, phi_t47_885441286927427630427, phi_t47_885441286927427630428, phi_t47_885441286927427630429, phi_t47_885441286927427630430, phi_t47_885441286927427630431, phi_t47_885441286927427630432, phi_t47_885441286927427630433, phi_t47_885441286927427630434, phi_t47_885441286927427630435, phi_t47_885441286927427630436, phi_t47_885441286927427630437, phi_t47_885441286927427630438, phi_t47_885441286927427630439, phi_t47_885441286927427630440, phi_t47_885441286927427630441, phi_t47_885441286927427630442, phi_t47_885441286927427630443, phi_t47_885441286927427630444, phi_t47_885441286927427630445, phi_t47_885441286927427630446, phi_t47_885441286927427630447, phi_t47_885441286927427630448, phi_t47_885441286927427630449, phi_t47_885441286927427630450, phi_t47_885441286927427630451, phi_t47_885441286927427630452, phi_t47_885441286927427630453, phi_t47_885441286927427630454, phi_t47_885441286927427630455, phi_t47_885441286927427630456, phi_t47_885441286927427630457, phi_t47_885441286927427630458, phi_t47_885441286927427630459, phi_t47_885441286927427630460, phi_t47_885441286927427630461, phi_t47_885441286927427630462, phi_t47_885441286927427630463, phi_t47_885441286927427630464, phi_t47_885441286927427630465, phi_t47_885441286927427630466, phi_t47_885441286927427630467, phi_t47_885441286927427630468, phi_t47_885441286927427630469, phi_t47_885441286927427630470, phi_t47_885441286927427630471, phi_t47_885441286927427630472, phi_t47_885441286927427630473]

def diagonalPincerCertificateScalesThroughT47 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47]

def diagonalPincerKillDepthThroughT47 : ℕ → ℕ
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
  | _ => 0

/-- All 23 imported scales through t=47 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t47 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT47,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT47 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT47, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t37
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t41
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t43
  · simpa [diagonalPincerKillDepthThroughT47] using certifiedKill_diagonal_t47

#print axioms certifiedKill_diagonal_all_imported_through_t47

end TotientTailPeriodKiller
end Erdos249257
