import Erdos249257.DiagonalPincerCertificatesT37
import Erdos249257.DiagonalPincerPrimeCertificates.Prime39404513
import Erdos249257.DiagonalPincerPrimeCertificates.Prime40185923
import Erdos249257.DiagonalPincerPrimeCertificates.Prime42406327
import Erdos249257.DiagonalPincerPrimeCertificates.Prime105485869
import Erdos249257.DiagonalPincerPrimeCertificates.Prime175611577
import Erdos249257.DiagonalPincerPrimeCertificates.Prime306555929
import Erdos249257.DiagonalPincerPrimeCertificates.Prime321535273
import Erdos249257.DiagonalPincerPrimeCertificates.Prime422621401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime608994259
import Erdos249257.DiagonalPincerPrimeCertificates.Prime689125061
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1526311613
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1931359517
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3064176299
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3337745129
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3580310791
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3930112903
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5092949023
import Erdos249257.DiagonalPincerPrimeCertificates.Prime9146224511
import Erdos249257.DiagonalPincerPrimeCertificates.Prime21369774403
import Erdos249257.DiagonalPincerPrimeCertificates.Prime23486071439
import Erdos249257.DiagonalPincerPrimeCertificates.Prime29535763981
import Erdos249257.DiagonalPincerPrimeCertificates.Prime36975198103
import Erdos249257.DiagonalPincerPrimeCertificates.Prime134340584141
import Erdos249257.DiagonalPincerPrimeCertificates.Prime173839495591
import Erdos249257.DiagonalPincerPrimeCertificates.Prime256434190891
import Erdos249257.DiagonalPincerPrimeCertificates.Prime268129824539
import Erdos249257.DiagonalPincerPrimeCertificates.Prime557015293979
import Erdos249257.DiagonalPincerPrimeCertificates.Prime600708832901
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1121685802999
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1198818966451
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1566225930287
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1780883040649
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2197325714081
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3987189707861
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4009301031143
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5238105468361
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5519001051587
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5615128221457
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10611324827533
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10915351524221
import Erdos249257.DiagonalPincerPrimeCertificates.Prime22590511471547
import Erdos249257.DiagonalPincerPrimeCertificates.Prime31988929576459
import Erdos249257.DiagonalPincerPrimeCertificates.Prime39498772041037
import Erdos249257.DiagonalPincerPrimeCertificates.Prime41583179525359
import Erdos249257.DiagonalPincerPrimeCertificates.Prime43215661814873
import Erdos249257.DiagonalPincerPrimeCertificates.Prime62535024190577
import Erdos249257.DiagonalPincerPrimeCertificates.Prime65235315586537
import Erdos249257.DiagonalPincerPrimeCertificates.Prime84874153328009
import Erdos249257.DiagonalPincerPrimeCertificates.Prime94300555204301
import Erdos249257.DiagonalPincerPrimeCertificates.Prime127434665351711
import Erdos249257.DiagonalPincerPrimeCertificates.Prime134392754441467
import Erdos249257.DiagonalPincerPrimeCertificates.Prime182778631405583
import Erdos249257.DiagonalPincerPrimeCertificates.Prime600988174868563
import Erdos249257.DiagonalPincerPrimeCertificates.Prime648107070235477
import Erdos249257.DiagonalPincerPrimeCertificates.Prime783757387261507
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1352223393454267
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1724883383776309
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2980410744756343
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3651003162326521
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3712884571857479
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3776899823096401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4868004216435361
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5764741835252401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime6638187567866401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime15107599292385601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime16850783826122401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime19048712151268801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime438120379479182443

/-!
# The t=41 diagonal-pincer certificate

This generated extension consumes 68 new large-prime Lucas roots
and 28 recursive Pratt dependencies, reuses 2 earlier certificates,
reconstructs all 122 Euler totients in the t=41 window, and proves the
twenty-first finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=41 window -/

private theorem prime_t41_2 : Nat.Prime 2 := by norm_num
private theorem prime_t41_3 : Nat.Prime 3 := by norm_num
private theorem prime_t41_5 : Nat.Prime 5 := by norm_num
private theorem prime_t41_7 : Nat.Prime 7 := by norm_num
private theorem prime_t41_11 : Nat.Prime 11 := by norm_num
private theorem prime_t41_13 : Nat.Prime 13 := by norm_num
private theorem prime_t41_17 : Nat.Prime 17 := by norm_num
private theorem prime_t41_19 : Nat.Prime 19 := by norm_num
private theorem prime_t41_23 : Nat.Prime 23 := by norm_num
private theorem prime_t41_29 : Nat.Prime 29 := by norm_num
private theorem prime_t41_31 : Nat.Prime 31 := by norm_num
private theorem prime_t41_37 : Nat.Prime 37 := by norm_num
private theorem prime_t41_41 : Nat.Prime 41 := by norm_num
private theorem prime_t41_43 : Nat.Prime 43 := by norm_num
private theorem prime_t41_47 : Nat.Prime 47 := by norm_num
private theorem prime_t41_53 : Nat.Prime 53 := by norm_num
private theorem prime_t41_59 : Nat.Prime 59 := by norm_num
private theorem prime_t41_61 : Nat.Prime 61 := by norm_num
private theorem prime_t41_67 : Nat.Prime 67 := by norm_num
private theorem prime_t41_71 : Nat.Prime 71 := by norm_num
private theorem prime_t41_73 : Nat.Prime 73 := by norm_num
private theorem prime_t41_79 : Nat.Prime 79 := by norm_num
private theorem prime_t41_89 : Nat.Prime 89 := by norm_num
private theorem prime_t41_97 : Nat.Prime 97 := by norm_num
private theorem prime_t41_101 : Nat.Prime 101 := by norm_num
private theorem prime_t41_103 : Nat.Prime 103 := by norm_num
private theorem prime_t41_107 : Nat.Prime 107 := by norm_num
private theorem prime_t41_109 : Nat.Prime 109 := by norm_num
private theorem prime_t41_113 : Nat.Prime 113 := by norm_num
private theorem prime_t41_127 : Nat.Prime 127 := by norm_num
private theorem prime_t41_137 : Nat.Prime 137 := by norm_num
private theorem prime_t41_139 : Nat.Prime 139 := by norm_num
private theorem prime_t41_149 : Nat.Prime 149 := by norm_num
private theorem prime_t41_157 : Nat.Prime 157 := by norm_num
private theorem prime_t41_163 : Nat.Prime 163 := by norm_num
private theorem prime_t41_173 : Nat.Prime 173 := by norm_num
private theorem prime_t41_179 : Nat.Prime 179 := by norm_num
private theorem prime_t41_181 : Nat.Prime 181 := by norm_num
private theorem prime_t41_191 : Nat.Prime 191 := by norm_num
private theorem prime_t41_193 : Nat.Prime 193 := by norm_num
private theorem prime_t41_199 : Nat.Prime 199 := by norm_num
private theorem prime_t41_229 : Nat.Prime 229 := by norm_num
private theorem prime_t41_233 : Nat.Prime 233 := by norm_num
private theorem prime_t41_263 : Nat.Prime 263 := by norm_num
private theorem prime_t41_271 : Nat.Prime 271 := by norm_num
private theorem prime_t41_277 : Nat.Prime 277 := by norm_num
private theorem prime_t41_293 : Nat.Prime 293 := by norm_num
private theorem prime_t41_313 : Nat.Prime 313 := by norm_num
private theorem prime_t41_353 : Nat.Prime 353 := by norm_num
private theorem prime_t41_373 : Nat.Prime 373 := by norm_num
private theorem prime_t41_379 : Nat.Prime 379 := by norm_num
private theorem prime_t41_397 : Nat.Prime 397 := by norm_num
private theorem prime_t41_409 : Nat.Prime 409 := by norm_num
private theorem prime_t41_419 : Nat.Prime 419 := by norm_num
private theorem prime_t41_439 : Nat.Prime 439 := by norm_num
private theorem prime_t41_479 : Nat.Prime 479 := by norm_num
private theorem prime_t41_509 : Nat.Prime 509 := by norm_num
private theorem prime_t41_547 : Nat.Prime 547 := by norm_num
private theorem prime_t41_631 : Nat.Prime 631 := by norm_num
private theorem prime_t41_733 : Nat.Prime 733 := by norm_num
private theorem prime_t41_827 : Nat.Prime 827 := by norm_num
private theorem prime_t41_947 : Nat.Prime 947 := by norm_num
private theorem prime_t41_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_t41_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_t41_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_t41_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_t41_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_t41_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_t41_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_t41_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_t41_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_t41_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_t41_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_t41_2243 : Nat.Prime 2243 := by norm_num
private theorem prime_t41_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_t41_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_t41_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_t41_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_t41_2543 : Nat.Prime 2543 := by norm_num
private theorem prime_t41_2659 : Nat.Prime 2659 := by norm_num
private theorem prime_t41_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_t41_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_t41_5231 : Nat.Prime 5231 := by norm_num
private theorem prime_t41_5717 : Nat.Prime 5717 := by norm_num
private theorem prime_t41_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_t41_6091 : Nat.Prime 6091 := by norm_num
private theorem prime_t41_6247 : Nat.Prime 6247 := by norm_num
private theorem prime_t41_6311 : Nat.Prime 6311 := by norm_num
private theorem prime_t41_6947 : Nat.Prime 6947 := by norm_num
private theorem prime_t41_7121 : Nat.Prime 7121 := by norm_num
private theorem prime_t41_7717 : Nat.Prime 7717 := by norm_num
private theorem prime_t41_8647 : Nat.Prime 8647 := by norm_num
private theorem prime_t41_9697 : Nat.Prime 9697 := by norm_num
private theorem prime_t41_9923 : Nat.Prime 9923 := by norm_num
private theorem prime_t41_10223 : Nat.Prime 10223 := by norm_num
private theorem prime_t41_10321 : Nat.Prime 10321 := by norm_num
private theorem prime_t41_13903 : Nat.Prime 13903 := by norm_num
private theorem prime_t41_15731 : Nat.Prime 15731 := by norm_num
private theorem prime_t41_18701 : Nat.Prime 18701 := by norm_num
private theorem prime_t41_21157 : Nat.Prime 21157 := by norm_num
private theorem prime_t41_21757 : Nat.Prime 21757 := by norm_num
private theorem prime_t41_22409 : Nat.Prime 22409 := by norm_num
private theorem prime_t41_23333 : Nat.Prime 23333 := by norm_num
private theorem prime_t41_23627 : Nat.Prime 23627 := by norm_num
private theorem prime_t41_25303 : Nat.Prime 25303 := by norm_num
private theorem prime_t41_25469 : Nat.Prime 25469 := by norm_num
private theorem prime_t41_26393 : Nat.Prime 26393 := by norm_num
private theorem prime_t41_30259 : Nat.Prime 30259 := by norm_num
private theorem prime_t41_40499 : Nat.Prime 40499 := by norm_num
private theorem prime_t41_43399 : Nat.Prime 43399 := by norm_num
private theorem prime_t41_54941 : Nat.Prime 54941 := by norm_num
private theorem prime_t41_75239 : Nat.Prime 75239 := by norm_num
private theorem prime_t41_83641 : Nat.Prime 83641 := by norm_num
private theorem prime_t41_86111 : Nat.Prime 86111 := by norm_num
private theorem prime_t41_87793 : Nat.Prime 87793 := by norm_num
private theorem prime_t41_100057 : Nat.Prime 100057 := by norm_num
private theorem prime_t41_104147 : Nat.Prime 104147 := by norm_num
private theorem prime_t41_111427 : Nat.Prime 111427 := by norm_num
private theorem prime_t41_113647 : Nat.Prime 113647 := by norm_num
private theorem prime_t41_115117 : Nat.Prime 115117 := by norm_num
private theorem prime_t41_116167 : Nat.Prime 116167 := by norm_num
private theorem prime_t41_119069 : Nat.Prime 119069 := by norm_num
private theorem prime_t41_122509 : Nat.Prime 122509 := by norm_num
private theorem prime_t41_133157 : Nat.Prime 133157 := by norm_num
private theorem prime_t41_138283 : Nat.Prime 138283 := by norm_num
private theorem prime_t41_145513 : Nat.Prime 145513 := by norm_num
private theorem prime_t41_170851 : Nat.Prime 170851 := by norm_num
private theorem prime_t41_195739 : Nat.Prime 195739 := by norm_num
private theorem prime_t41_231019 : Nat.Prime 231019 := by norm_num
private theorem prime_t41_269701 : Nat.Prime 269701 := by norm_num
private theorem prime_t41_302999 : Nat.Prime 302999 := by norm_num
private theorem prime_t41_305353 : Nat.Prime 305353 := by norm_num
private theorem prime_t41_308219 : Nat.Prime 308219 := by norm_num
private theorem prime_t41_420191 : Nat.Prime 420191 := by norm_num
private theorem prime_t41_645041 : Nat.Prime 645041 := by norm_num
private theorem prime_t41_784789 : Nat.Prime 784789 := by norm_num
private theorem prime_t41_855187 : Nat.Prime 855187 := by norm_num
private theorem prime_t41_1156013 : Nat.Prime 1156013 := by norm_num
private theorem prime_t41_1181617 : Nat.Prime 1181617 := by norm_num
private theorem prime_t41_1232563 : Nat.Prime 1232563 := by norm_num
private theorem prime_t41_1272629 : Nat.Prime 1272629 := by norm_num
private theorem prime_t41_1281367 : Nat.Prime 1281367 := by norm_num
private theorem prime_t41_1305247 : Nat.Prime 1305247 := by norm_num
private theorem prime_t41_1630633 : Nat.Prime 1630633 := by norm_num
private theorem prime_t41_1987519 : Nat.Prime 1987519 := by norm_num
private theorem prime_t41_2990017 : Nat.Prime 2990017 := by norm_num
private theorem prime_t41_3844273 : Nat.Prime 3844273 := by norm_num
private theorem prime_t41_5620469 : Nat.Prime 5620469 := by norm_num
private theorem prime_t41_6218159 : Nat.Prime 6218159 := by norm_num
private theorem prime_t41_6824777 : Nat.Prime 6824777 := by norm_num
private theorem prime_t41_7973477 : Nat.Prime 7973477 := by norm_num
private theorem prime_t41_10173811 : Nat.Prime 10173811 := by norm_num
private theorem prime_t41_12772433 : Nat.Prime 12772433 := by norm_num
private theorem prime_t41_13113077 : Nat.Prime 13113077 := by norm_num
private theorem prime_t41_13482731 : Nat.Prime 13482731 := by norm_num
private theorem prime_t41_14531747 : Nat.Prime 14531747 := by norm_num
private theorem prime_t41_15867463 : Nat.Prime 15867463 := by norm_num
private theorem prime_t41_18751769 : Nat.Prime 18751769 := by norm_num
private theorem prime_t41_19370159 : Nat.Prime 19370159 := by norm_num
private theorem prime_t41_23521501 : Nat.Prime 23521501 := by norm_num
private theorem prime_t41_25630177 : Nat.Prime 25630177 := by norm_num
private theorem prime_t41_29700313 : Nat.Prime 29700313 := by norm_num
private theorem prime_t41_32547331 : Nat.Prime 32547331 := by norm_num

/-! ## Exact t=41 window totients -/

private theorem phi_t41_219060189739591201 : Nat.totient 219060189739591201 = 219056202549828400 := by
  rw [← show ((([(54941, 1), (3987189707861, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_54941, prime_lucas_3987189707861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591202 : Nat.totient 219060189739591202 = 105382723805484048 := by
  rw [← show ((([(2, 1), (47, 1), (59, 1), (39498772041037, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_47, prime_t41_59, prime_lucas_39498772041037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591203 : Nat.totient 219060189739591203 = 145961852363706240 := by
  rw [← show ((([(3, 1), (1867, 1), (3844273, 1), (10173811, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_1867, prime_t41_3844273, prime_t41_10173811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591204 : Nat.totient 219060189739591204 = 109519056867672584 := by
  rw [← show ((([(2, 2), (9923, 1), (5519001051587, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_9923, prime_lucas_5519001051587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591205 : Nat.totient 219060189739591205 = 175247126054226000 := by
  rw [← show ((([(5, 1), (170851, 1), (256434190891, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_170851, prime_lucas_256434190891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591206 : Nat.totient 219060189739591206 = 73016332041014784 := by
  rw [← show ((([(2, 1), (3, 1), (23333, 1), (122509, 1), (12772433, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_23333, prime_t41_122509, prime_t41_12772433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591207 : Nat.totient 219060189739591207 = 186257553059743200 := by
  rw [← show ((([(7, 1), (139, 1), (2351, 1), (2383, 1), (40185923, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_7, prime_t41_139, prime_t41_2351, prime_t41_2383, prime_lucas_40185923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591208 : Nat.totient 219060189739591208 = 109530009385572528 := by
  rw [← show ((([(2, 3), (1281367, 1), (21369774403, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_1281367, prime_lucas_21369774403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591209 : Nat.totient 219060189739591209 = 145275518500949400 := by
  rw [← show ((([(3, 2), (191, 1), (127434665351711, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_191, prime_lucas_127434665351711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591210 : Nat.totient 219060189739591210 = 87086504878069968 := by
  rw [← show ((([(2, 1), (5, 1), (163, 1), (134392754441467, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_163, prime_lucas_134392754441467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591211 : Nat.totient 219060189739591211 = 199099997620937600 := by
  rw [← show ((([(11, 2), (5231, 1), (26393, 1), (13113077, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_11, prime_t41_5231, prime_t41_26393, prime_t41_13113077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591212 : Nat.totient 219060189739591212 = 72853730528427216 := by
  rw [← show ((([(2, 2), (3, 1), (439, 1), (41583179525359, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_439, prime_lucas_41583179525359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591213 : Nat.totient 219060189739591213 = 202209405913468800 := by
  rw [← show ((([(13, 1), (16850783826122401, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_13, prime_lucas_16850783826122401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591214 : Nat.totient 219060189739591214 = 93869754505497600 := by
  rw [← show ((([(2, 1), (7, 1), (7121, 1), (2197325714081, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_7, prime_t41_7121, prime_lucas_2197325714081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591215 : Nat.totient 219060189739591215 = 114171980666325120 := by
  rw [← show ((([(3, 1), (5, 1), (71, 1), (199, 1), (263, 1), (3930112903, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_5, prime_t41_71, prime_t41_199, prime_t41_263, prime_lucas_3930112903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591216 : Nat.totient 219060189739591216 = 109023899748009984 := by
  rw [← show ((([(2, 4), (233, 1), (3539, 1), (21157, 1), (784789, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_233, prime_t41_3539, prime_t41_21157, prime_t41_784789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591217 : Nat.totient 219060189739591217 = 203540495883033600 := by
  rw [← show ((([(17, 2), (181, 2), (271, 1), (277, 1), (308219, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_17, prime_t41_181, prime_t41_271, prime_t41_277, prime_t41_308219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591218 : Nat.totient 219060189739591218 = 73020054040819872 := by
  rw [← show ((([(2, 1), (3, 2), (7973477, 1), (1526311613, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_7973477, prime_lucas_1526311613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591219 : Nat.totient 219060189739591219 = 207390072447068544 := by
  rw [← show ((([(19, 1), (2069, 1), (8647, 1), (25303, 1), (25469, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_19, prime_t41_2069, prime_t41_8647, prime_t41_25303, prime_t41_25469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591220 : Nat.totient 219060189739591220 = 87611070594157824 := by
  rw [← show ((([(2, 2), (5, 1), (6947, 1), (231019, 1), (6824777, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_6947, prime_t41_231019, prime_t41_6824777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591221 : Nat.totient 219060189739591221 = 124630514754729984 := by
  rw [← show ((([(3, 1), (7, 1), (229, 1), (1156013, 1), (39404513, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_7, prime_t41_229, prime_t41_1156013, prime_lucas_39404513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591222 : Nat.totient 219060189739591222 = 99564017618664480 := by
  rw [← show ((([(2, 1), (11, 1), (21757, 1), (23627, 1), (19370159, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_11, prime_t41_21757, prime_t41_23627, prime_t41_19370159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591223 : Nat.totient 219060189739591223 = 207461221449460000 := by
  rw [← show ((([(23, 1), (101, 1), (94300555204301, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_23, prime_t41_101, prime_lucas_94300555204301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591224 : Nat.totient 219060189739591224 = 72310633535598336 := by
  rw [← show ((([(2, 3), (3, 1), (103, 1), (145513, 1), (608994259, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_103, prime_t41_145513, prime_lucas_608994259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591225 : Nat.totient 219060189739591225 = 175237011485478800 := by
  rw [← show ((([(5, 2), (15731, 1), (557015293979, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_15731, prime_lucas_557015293979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591226 : Nat.totient 219060189739591226 = 101104702956734256 := by
  rw [← show ((([(2, 1), (13, 2), (648107070235477, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_13, prime_lucas_648107070235477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591227 : Nat.totient 219060189739591227 = 146035300155674472 := by
  rw [← show ((([(3, 3), (30259, 1), (268129824539, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_30259, prime_lucas_268129824539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591228 : Nat.totient 219060189739591228 = 91612939705056000 := by
  rw [← show ((([(2, 2), (7, 1), (43, 1), (1283, 1), (6029, 1), (23521501, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_7, prime_t41_43, prime_t41_1283, prime_t41_6029, prime_t41_23521501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591229 : Nat.totient 219060189739591229 = 209129913800211712 := by
  rw [← show ((([(29, 1), (89, 1), (84874153328009, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_29, prime_t41_89, prime_lucas_84874153328009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591230 : Nat.totient 219060189739591230 = 58406460045444000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (6091, 1), (1198818966451, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_5, prime_t41_6091, prime_lucas_1198818966451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591231 : Nat.totient 219060189739591231 = 210117681280335360 := by
  rw [← show ((([(31, 1), (113, 1), (62535024190577, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_31, prime_t41_113, prime_lucas_62535024190577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591232 : Nat.totient 219060189739591232 = 108506449123345536 := by
  rw [← show ((([(2, 6), (107, 1), (31988929576459, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_107, prime_lucas_31988929576459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591233 : Nat.totient 219060189739591233 = 132763751357328000 := by
  rw [← show ((([(3, 1), (11, 1), (6638187567866401, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_11, prime_lucas_6638187567866401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591234 : Nat.totient 219060189739591234 = 103022999296224832 := by
  rw [← show ((([(2, 1), (17, 1), (1607, 1), (4009301031143, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_17, prime_t41_1607, prime_lucas_4009301031143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591235 : Nat.totient 219060189739591235 = 149854198638668832 := by
  rw [← show ((([(5, 1), (7, 2), (419, 2), (5092949023, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_7, prime_t41_419, prime_lucas_5092949023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591236 : Nat.totient 219060189739591236 = 73007735023399680 := by
  rw [← show ((([(2, 2), (3, 2), (10321, 1), (13903, 1), (42406327, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_10321, prime_t41_13903, prime_lucas_42406327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591237 : Nat.totient 219060189739591237 = 211583880245613312 := by
  rw [← show ((([(37, 1), (137, 1), (43215661814873, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_37, prime_t41_137, prime_lucas_43215661814873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591238 : Nat.totient 219060189739591238 = 103765353034543200 := by
  rw [← show ((([(2, 1), (19, 1), (5764741835252401, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_19, prime_lucas_5764741835252401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591239 : Nat.totient 219060189739591239 = 132774434583747840 := by
  rw [← show ((([(3, 1), (13, 1), (79, 1), (409, 1), (173839495591, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_13, prime_t41_79, prime_t41_409, prime_lucas_173839495591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591240 : Nat.totient 219060189739591240 = 87337567740494848 := by
  rw [← show ((([(2, 3), (5, 1), (509, 1), (827, 1), (10223, 1), (1272629, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_509, prime_t41_827, prime_t41_10223, prime_t41_1272629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591241 : Nat.totient 219060189739591241 = 212481898408055680 := by
  rw [← show ((([(41, 1), (173, 1), (30883996861637, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_41, prime_t41_173, prime_lucas_30883996861637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591242 : Nat.totient 219060189739591242 = 62588623176140544 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (29700313, 1), (175611577, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_7, prime_t41_29700313, prime_lucas_175611577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591243 : Nat.totient 219060189739591243 = 217335306355814808 := by
  rw [← show ((([(127, 1), (1724883383776309, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_127, prime_lucas_1724883383776309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591244 : Nat.totient 219060189739591244 = 99528203489682240 := by
  rw [← show ((([(2, 2), (11, 1), (2269, 1), (138283, 1), (15867463, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_11, prime_t41_2269, prime_t41_138283, prime_t41_15867463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591245 : Nat.totient 219060189739591245 = 116832101194448640 := by
  rw [← show ((([(3, 2), (5, 1), (4868004216435361, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_5, prime_lucas_4868004216435361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591246 : Nat.totient 219060189739591246 = 103332739889073024 := by
  rw [← show ((([(2, 1), (23, 1), (73, 1), (65235315586537, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_23, prime_t41_73, prime_lucas_65235315586537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591247 : Nat.totient 219060189739591247 = 214926961970418880 := by
  rw [← show ((([(53, 1), (13482731, 1), (306555929, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_53, prime_t41_13482731, prime_lucas_306555929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591248 : Nat.totient 219060189739591248 = 72330736102410240 := by
  rw [← show ((([(2, 4), (3, 1), (293, 1), (379, 1), (547, 1), (631, 1), (119069, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_293, prime_t41_379, prime_t41_547, prime_t41_631, prime_t41_119069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591249 : Nat.totient 219060189739591249 = 180758221241083200 := by
  rw [← show ((([(7, 1), (47, 1), (61, 1), (10915351524221, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_7, prime_t41_47, prime_t41_61, prime_lucas_10915351524221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591250 : Nat.totient 219060189739591250 = 87065792248968000 := by
  rw [← show ((([(2, 1), (5, 4), (157, 1), (855187, 1), (1305247, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_157, prime_t41_855187, prime_t41_1305247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591251 : Nat.totient 219060189739591251 = 137448347606941824 := by
  rw [← show ((([(3, 1), (17, 1), (116167, 1), (36975198103, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_17, prime_t41_116167, prime_lucas_36975198103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591252 : Nat.totient 219060189739591252 = 100850031160864128 := by
  rw [← show ((([(2, 2), (13, 1), (397, 1), (10611324827533, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_13, prime_t41_397, prime_lucas_10611324827533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591253 : Nat.totient 219060189739591253 = 219060055397376480 := by
  rw [← show ((([(1630633, 1), (134340584141, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_1630633, prime_lucas_134340584141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591254 : Nat.totient 219060189739591254 = 73020063246530364 := by
  rw [← show ((([(2, 1), (3, 4), (1352223393454267, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_lucas_1352223393454267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591255 : Nat.totient 219060189739591255 = 159253852591480480 := by
  rw [← show ((([(5, 1), (11, 1), (2543, 1), (1566225930287, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_11, prime_t41_2543, prime_lucas_1566225930287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591256 : Nat.totient 219060189739591256 = 92385730975317120 := by
  rw [← show ((([(2, 3), (7, 1), (67, 1), (1511, 1), (2659, 1), (14531747, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_7, prime_t41_67, prime_t41_1511, prime_t41_2659, prime_t41_14531747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591257 : Nat.totient 219060189739591257 = 138353474766848400 := by
  rw [← show ((([(3, 1), (19, 1), (420191, 1), (9146224511, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_19, prime_t41_420191, prime_lucas_9146224511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591258 : Nat.totient 219060189739591258 = 105753195046699200 := by
  rw [← show ((([(2, 1), (29, 1), (3776899823096401, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_29, prime_lucas_3776899823096401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591259 : Nat.totient 219060189739591259 = 219037599228110016 := by
  rw [← show ((([(9697, 1), (22590511471547, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_9697, prime_lucas_22590511471547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591260 : Nat.totient 219060189739591260 = 58416050597224320 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (3651003162326521, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_5, prime_lucas_3651003162326521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_219060189739591261 : Nat.totient 219060189739591261 = 215347305167733724 := by
  rw [← show ((([(59, 1), (3712884571857479, 1)] : List FactorBlock).map factorBlockValue).prod) = 219060189739591261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_59, prime_lucas_3712884571857479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182401 : Nat.totient 438120379479182401 = 438115141373630400 := by
  rw [← show ((([(83641, 1), (5238105468361, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_83641, prime_lucas_5238105468361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182402 : Nat.totient 438120379479182402 = 219056202549828400 := by
  rw [← show ((([(2, 1), (54941, 1), (3987189707861, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_54941, prime_lucas_3987189707861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182403 : Nat.totient 438120379479182403 = 292080206001542408 := by
  rw [← show ((([(3, 1), (6218159, 1), (23486071439, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_6218159, prime_lucas_23486071439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182404 : Nat.totient 438120379479182404 = 210765447610968096 := by
  rw [← show ((([(2, 2), (47, 1), (59, 1), (39498772041037, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_47, prime_t41_59, prime_lucas_39498772041037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182405 : Nat.totient 438120379479182405 = 349764505546841280 := by
  rw [← show ((([(5, 1), (479, 1), (5620469, 1), (32547331, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_479, prime_t41_5620469, prime_t41_32547331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182406 : Nat.totient 438120379479182406 = 145961852363706240 := by
  rw [← show ((([(2, 1), (3, 1), (1867, 1), (3844273, 1), (10173811, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_1867, prime_t41_3844273, prime_t41_10173811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182407 : Nat.totient 438120379479182407 = 375531733700317824 := by
  rw [← show ((([(7, 1), (18751769, 1), (3337745129, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_7, prime_t41_18751769, prime_lucas_3337745129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182408 : Nat.totient 438120379479182408 = 219038113735345168 := by
  rw [← show ((([(2, 3), (9923, 1), (5519001051587, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_9923, prime_lucas_5519001051587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182409 : Nat.totient 438120379479182409 = 292073522871043224 := by
  rw [← show ((([(3, 2), (43399, 1), (1121685802999, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_43399, prime_lucas_1121685802999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182410 : Nat.totient 438120379479182410 = 175247126054226000 := by
  rw [← show ((([(2, 1), (5, 1), (170851, 1), (256434190891, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_170851, prime_lucas_256434190891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182411 : Nat.totient 438120379479182411 = 396394288438233600 := by
  rw [← show ((([(11, 1), (373, 1), (733, 1), (1381, 1), (105485869, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_11, prime_t41_373, prime_t41_733, prime_t41_1381, prime_lucas_105485869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182412 : Nat.totient 438120379479182412 = 146032664082029568 := by
  rw [← show ((([(2, 2), (3, 1), (23333, 1), (122509, 1), (12772433, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_23333, prime_t41_122509, prime_t41_12772433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182413 : Nat.totient 438120379479182413 = 395013723179799024 := by
  rw [← show ((([(13, 1), (43, 1), (783757387261507, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_13, prime_t41_43, prime_lucas_783757387261507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182414 : Nat.totient 438120379479182414 = 186257553059743200 := by
  rw [← show ((([(2, 1), (7, 1), (139, 1), (2351, 1), (2383, 1), (40185923, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_7, prime_t41_139, prime_t41_2351, prime_t41_2383, prime_lucas_40185923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182415 : Nat.totient 438120379479182415 = 233554259749698816 := by
  rw [← show ((([(3, 1), (5, 1), (2243, 1), (40499, 1), (321535273, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_5, prime_t41_2243, prime_t41_40499, prime_lucas_321535273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182416 : Nat.totient 438120379479182416 = 219060018771145056 := by
  rw [← show ((([(2, 4), (1281367, 1), (21369774403, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_1281367, prime_lucas_21369774403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182417 : Nat.totient 438120379479182417 = 412342436263984128 := by
  rw [← show ((([(17, 1), (111427, 1), (195739, 1), (1181617, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_17, prime_t41_111427, prime_t41_195739, prime_t41_1181617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182418 : Nat.totient 438120379479182418 = 145275518500949400 := by
  rw [← show ((([(2, 1), (3, 2), (191, 1), (127434665351711, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_191, prime_lucas_127434665351711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182419 : Nat.totient 438120379479182419 = 404970855758364672 := by
  rw [← show ((([(19, 1), (73, 1), (179, 1), (193, 1), (87793, 1), (104147, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_19, prime_t41_73, prime_t41_179, prime_t41_193, prime_t41_87793, prime_t41_104147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182420 : Nat.totient 438120379479182420 = 174173009756139936 := by
  rw [← show ((([(2, 2), (5, 1), (163, 1), (134392754441467, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_163, prime_lucas_134392754441467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182421 : Nat.totient 438120379479182421 = 250354502559532728 := by
  rw [← show ((([(3, 1), (7, 2), (2980410744756343, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_7, prime_lucas_2980410744756343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182422 : Nat.totient 438120379479182422 = 199099997620937600 := by
  rw [← show ((([(2, 1), (11, 2), (5231, 1), (26393, 1), (13113077, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_11, prime_t41_5231, prime_t41_26393, prime_t41_13113077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182423 : Nat.totient 438120379479182423 = 419071667327913600 := by
  rw [← show ((([(23, 1), (19048712151268801, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_23, prime_lucas_19048712151268801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182424 : Nat.totient 438120379479182424 = 145707461056854432 := by
  rw [← show ((([(2, 3), (3, 1), (439, 1), (41583179525359, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_439, prime_lucas_41583179525359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182425 : Nat.totient 438120379479182425 = 350384001018854400 := by
  rw [← show ((([(5, 2), (3121, 1), (5615128221457, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_3121, prime_lucas_5615128221457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182426 : Nat.totient 438120379479182426 = 202209405913468800 := by
  rw [← show ((([(2, 1), (13, 1), (16850783826122401, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_13, prime_lucas_16850783826122401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182427 : Nat.totient 438120379479182427 = 292080252986121132 := by
  rw [← show ((([(3, 6), (600988174868563, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_lucas_600988174868563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182428 : Nat.totient 438120379479182428 = 187739509010995200 := by
  rw [← show ((([(2, 2), (7, 1), (7121, 1), (2197325714081, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_7, prime_t41_7121, prime_lucas_2197325714081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182429 : Nat.totient 438120379479182429 = 423012780186796800 := by
  rw [← show ((([(29, 1), (15107599292385601, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_29, prime_lucas_15107599292385601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182430 : Nat.totient 438120379479182430 = 114171980666325120 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (71, 1), (199, 1), (263, 1), (3930112903, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_5, prime_t41_71, prime_t41_199, prime_t41_263, prime_lucas_3930112903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182431 : Nat.totient 438120379479182431 = 423979012218477600 := by
  rw [← show ((([(31, 1), (86111, 1), (133157, 1), (1232563, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_31, prime_t41_86111, prime_t41_133157, prime_t41_1232563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182432 : Nat.totient 438120379479182432 = 218047799496019968 := by
  rw [← show ((([(2, 5), (233, 1), (3539, 1), (21157, 1), (784789, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_233, prime_t41_3539, prime_t41_21157, prime_t41_784789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182433 : Nat.totient 438120379479182433 = 264624120279567360 := by
  rw [← show ((([(3, 1), (11, 1), (313, 1), (6247, 1), (22409, 1), (302999, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_11, prime_t41_313, prime_t41_6247, prime_t41_22409, prime_t41_302999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182434 : Nat.totient 438120379479182434 = 203540495883033600 := by
  rw [← show ((([(2, 1), (17, 2), (181, 2), (271, 1), (277, 1), (308219, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_17, prime_t41_181, prime_t41_271, prime_t41_277, prime_t41_308219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182435 : Nat.totient 438120379479182435 = 297327259544371200 := by
  rw [← show ((([(5, 1), (7, 1), (97, 1), (305353, 1), (422621401, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_7, prime_t41_97, prime_t41_305353, prime_lucas_422621401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182436 : Nat.totient 438120379479182436 = 146040108081639744 := by
  rw [← show ((([(2, 2), (3, 2), (7973477, 1), (1526311613, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_7973477, prime_lucas_1526311613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182437 : Nat.totient 438120379479182437 = 415444395722365440 := by
  rw [← show ((([(37, 1), (61, 1), (109, 1), (1780883040649, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_37, prime_t41_61, prime_t41_109, prime_lucas_1780883040649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182438 : Nat.totient 438120379479182438 = 207390072447068544 := by
  rw [← show ((([(2, 1), (19, 1), (2069, 1), (8647, 1), (25303, 1), (25469, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_19, prime_t41_2069, prime_t41_8647, prime_t41_25303, prime_t41_25469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182439 : Nat.totient 438120379479182439 = 269598124205520000 := by
  rw [← show ((([(3, 1), (13, 1), (18701, 1), (600708832901, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_13, prime_t41_18701, prime_lucas_600708832901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182440 : Nat.totient 438120379479182440 = 175222141188315648 := by
  rw [← show ((([(2, 3), (5, 1), (6947, 1), (231019, 1), (6824777, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_6947, prime_t41_231019, prime_t41_6824777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182441 : Nat.totient 438120379479182441 = 416334635716280320 := by
  rw [← show ((([(41, 1), (53, 1), (149, 1), (1889, 1), (716333897, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_41, prime_t41_53, prime_t41_149, prime_t41_1889, prime_lucas_716333897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182442 : Nat.totient 438120379479182442 = 124630514754729984 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (229, 1), (1156013, 1), (39404513, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_7, prime_t41_229, prime_t41_1156013, prime_lucas_39404513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182443 : Nat.totient 438120379479182443 = 438120379479182442 := by
  rw [← show ((([(438120379479182443, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_438120379479182443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182444 : Nat.totient 438120379479182444 = 199128035237328960 := by
  rw [← show ((([(2, 2), (11, 1), (21757, 1), (23627, 1), (19370159, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_11, prime_t41_21757, prime_t41_23627, prime_t41_19370159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182445 : Nat.totient 438120379479182445 = 230173617587455872 := by
  rw [← show ((([(3, 2), (5, 1), (67, 1), (75239, 1), (1931359517, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_5, prime_t41_67, prime_t41_75239, prime_lucas_1931359517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182446 : Nat.totient 438120379479182446 = 207461221449460000 := by
  rw [← show ((([(2, 1), (23, 1), (101, 1), (94300555204301, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_23, prime_t41_101, prime_lucas_94300555204301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182447 : Nat.totient 438120379479182447 = 437809411404598464 := by
  rw [← show ((([(1429, 1), (100057, 1), (3064176299, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_1429, prime_t41_100057, prime_lucas_3064176299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182448 : Nat.totient 438120379479182448 = 144621267071196672 := by
  rw [← show ((([(2, 4), (3, 1), (103, 1), (145513, 1), (608994259, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_103, prime_t41_145513, prime_lucas_608994259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182449 : Nat.totient 438120379479182449 = 375108496490257920 := by
  rw [← show ((([(7, 1), (1789, 1), (2281, 1), (7717, 1), (1987519, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_7, prime_t41_1789, prime_t41_2281, prime_t41_7717, prime_t41_1987519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182450 : Nat.totient 438120379479182450 = 175237011485478800 := by
  rw [← show ((([(2, 1), (5, 2), (15731, 1), (557015293979, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_5, prime_t41_15731, prime_lucas_557015293979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182451 : Nat.totient 438120379479182451 = 269050145429016704 := by
  rw [← show ((([(3, 1), (17, 1), (47, 1), (182778631405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_17, prime_t41_47, prime_lucas_182778631405583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182452 : Nat.totient 438120379479182452 = 202209405913468512 := by
  rw [← show ((([(2, 2), (13, 2), (648107070235477, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_13, prime_lucas_648107070235477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182453 : Nat.totient 438120379479182453 = 438043581221216256 := by
  rw [← show ((([(5717, 1), (2990017, 1), (25630177, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5717, prime_t41_2990017, prime_t41_25630177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182454 : Nat.totient 438120379479182454 = 146035300155674472 := by
  rw [← show ((([(2, 1), (3, 3), (30259, 1), (268129824539, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_30259, prime_lucas_268129824539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182455 : Nat.totient 438120379479182455 = 318631821816240000 := by
  rw [← show ((([(5, 1), (11, 1), (269701, 1), (29535763981, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_5, prime_t41_11, prime_t41_269701, prime_lucas_29535763981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182456 : Nat.totient 438120379479182456 = 183225879410112000 := by
  rw [← show ((([(2, 3), (7, 1), (43, 1), (1283, 1), (6029, 1), (23521501, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_7, prime_t41_43, prime_t41_1283, prime_t41_6029, prime_t41_23521501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182457 : Nat.totient 438120379479182457 = 275757814185384960 := by
  rw [← show ((([(3, 1), (19, 2), (353, 1), (1663, 1), (689125061, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_3, prime_t41_19, prime_t41_353, prime_t41_1663, prime_lucas_689125061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182458 : Nat.totient 438120379479182458 = 209129913800211712 := by
  rw [← show ((([(2, 1), (29, 1), (89, 1), (84874153328009, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_29, prime_t41_89, prime_lucas_84874153328009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182459 : Nat.totient 438120379479182459 = 437583861965078400 := by
  rw [← show ((([(947, 1), (6311, 1), (113647, 1), (645041, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_947, prime_t41_6311, prime_t41_113647, prime_t41_645041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182460 : Nat.totient 438120379479182460 = 116812920090888000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (6091, 1), (1198818966451, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_2, prime_t41_3, prime_t41_5, prime_t41_6091, prime_lucas_1198818966451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t41_438120379479182461 : Nat.totient 438120379479182461 = 437704422429541680 := by
  rw [← show ((([(1063, 1), (115117, 1), (3580310791, 1)] : List FactorBlock).map factorBlockValue).prod) = 438120379479182461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t41_1063, prime_t41_115117, prime_lucas_3580310791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twenty-first finite diagonal certificate -/

theorem certifiedKill_diagonal_t41 :
    certifiedKill (periodLcm 41) (periodLcm 41) 61 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t41_219060189739591201, phi_t41_219060189739591202, phi_t41_219060189739591203, phi_t41_219060189739591204, phi_t41_219060189739591205, phi_t41_219060189739591206, phi_t41_219060189739591207, phi_t41_219060189739591208, phi_t41_219060189739591209, phi_t41_219060189739591210, phi_t41_219060189739591211, phi_t41_219060189739591212, phi_t41_219060189739591213, phi_t41_219060189739591214, phi_t41_219060189739591215, phi_t41_219060189739591216, phi_t41_219060189739591217, phi_t41_219060189739591218, phi_t41_219060189739591219, phi_t41_219060189739591220, phi_t41_219060189739591221, phi_t41_219060189739591222, phi_t41_219060189739591223, phi_t41_219060189739591224, phi_t41_219060189739591225, phi_t41_219060189739591226, phi_t41_219060189739591227, phi_t41_219060189739591228, phi_t41_219060189739591229, phi_t41_219060189739591230, phi_t41_219060189739591231, phi_t41_219060189739591232, phi_t41_219060189739591233, phi_t41_219060189739591234, phi_t41_219060189739591235, phi_t41_219060189739591236, phi_t41_219060189739591237, phi_t41_219060189739591238, phi_t41_219060189739591239, phi_t41_219060189739591240, phi_t41_219060189739591241, phi_t41_219060189739591242, phi_t41_219060189739591243, phi_t41_219060189739591244, phi_t41_219060189739591245, phi_t41_219060189739591246, phi_t41_219060189739591247, phi_t41_219060189739591248, phi_t41_219060189739591249, phi_t41_219060189739591250, phi_t41_219060189739591251, phi_t41_219060189739591252, phi_t41_219060189739591253, phi_t41_219060189739591254, phi_t41_219060189739591255, phi_t41_219060189739591256, phi_t41_219060189739591257, phi_t41_219060189739591258, phi_t41_219060189739591259, phi_t41_219060189739591260, phi_t41_219060189739591261, phi_t41_438120379479182401, phi_t41_438120379479182402, phi_t41_438120379479182403, phi_t41_438120379479182404, phi_t41_438120379479182405, phi_t41_438120379479182406, phi_t41_438120379479182407, phi_t41_438120379479182408, phi_t41_438120379479182409, phi_t41_438120379479182410, phi_t41_438120379479182411, phi_t41_438120379479182412, phi_t41_438120379479182413, phi_t41_438120379479182414, phi_t41_438120379479182415, phi_t41_438120379479182416, phi_t41_438120379479182417, phi_t41_438120379479182418, phi_t41_438120379479182419, phi_t41_438120379479182420, phi_t41_438120379479182421, phi_t41_438120379479182422, phi_t41_438120379479182423, phi_t41_438120379479182424, phi_t41_438120379479182425, phi_t41_438120379479182426, phi_t41_438120379479182427, phi_t41_438120379479182428, phi_t41_438120379479182429, phi_t41_438120379479182430, phi_t41_438120379479182431, phi_t41_438120379479182432, phi_t41_438120379479182433, phi_t41_438120379479182434, phi_t41_438120379479182435, phi_t41_438120379479182436, phi_t41_438120379479182437, phi_t41_438120379479182438, phi_t41_438120379479182439, phi_t41_438120379479182440, phi_t41_438120379479182441, phi_t41_438120379479182442, phi_t41_438120379479182443, phi_t41_438120379479182444, phi_t41_438120379479182445, phi_t41_438120379479182446, phi_t41_438120379479182447, phi_t41_438120379479182448, phi_t41_438120379479182449, phi_t41_438120379479182450, phi_t41_438120379479182451, phi_t41_438120379479182452, phi_t41_438120379479182453, phi_t41_438120379479182454, phi_t41_438120379479182455, phi_t41_438120379479182456, phi_t41_438120379479182457, phi_t41_438120379479182458, phi_t41_438120379479182459, phi_t41_438120379479182460, phi_t41_438120379479182461]

def diagonalPincerCertificateScalesThroughT41 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41]

def diagonalPincerKillDepthThroughT41 : ℕ → ℕ
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
  | _ => 0

/-- All 21 imported scales through t=41 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t41 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT41,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT41 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT41, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t37
  · simpa [diagonalPincerKillDepthThroughT41] using certifiedKill_diagonal_t41

#print axioms certifiedKill_diagonal_all_imported_through_t41

end TotientTailPeriodKiller
end Erdos249257
