import Erdos249257.DiagonalPincerCertificatesT27
import Erdos249257.DiagonalPincerPrimeCertificates.Prime34581109
import Erdos249257.DiagonalPincerPrimeCertificates.Prime37726603
import Erdos249257.DiagonalPincerPrimeCertificates.Prime46078157
import Erdos249257.DiagonalPincerPrimeCertificates.Prime48276289
import Erdos249257.DiagonalPincerPrimeCertificates.Prime60753047
import Erdos249257.DiagonalPincerPrimeCertificates.Prime120543931
import Erdos249257.DiagonalPincerPrimeCertificates.Prime168585253
import Erdos249257.DiagonalPincerPrimeCertificates.Prime191238161
import Erdos249257.DiagonalPincerPrimeCertificates.Prime255550753
import Erdos249257.DiagonalPincerPrimeCertificates.Prime444482741
import Erdos249257.DiagonalPincerPrimeCertificates.Prime542848051
import Erdos249257.DiagonalPincerPrimeCertificates.Prime567240517
import Erdos249257.DiagonalPincerPrimeCertificates.Prime709871857
import Erdos249257.DiagonalPincerPrimeCertificates.Prime842347039
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1413711419
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1519301737
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1872258491
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4758099209
import Erdos249257.DiagonalPincerPrimeCertificates.Prime7079299583
import Erdos249257.DiagonalPincerPrimeCertificates.Prime25454530741
import Erdos249257.DiagonalPincerPrimeCertificates.Prime36392024419
import Erdos249257.DiagonalPincerPrimeCertificates.Prime61291830601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime68502634201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime77636318761
import Erdos249257.DiagonalPincerPrimeCertificates.Prime86262576401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime89580367801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime103515091681
import Erdos249257.DiagonalPincerPrimeCertificates.Prime116454478141
import Erdos249257.DiagonalPincerPrimeCertificates.Prime119440490401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime129393864601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime232908956281
import Erdos249257.DiagonalPincerPrimeCertificates.Prime258787729201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime274010536801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime358321471201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime388181593801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime665454160801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2329089562843

/-!
# The t=29 diagonal-pincer certificate

This generated extension consumes 37 new large-prime Lucas roots
and 2 recursive Pratt dependencies, reuses 0 earlier certificates,
reconstructs all 90 Euler totients in the t=29 window, and proves the
seventeenth finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=29 window -/

private theorem prime_t29_2 : Nat.Prime 2 := by norm_num
private theorem prime_t29_3 : Nat.Prime 3 := by norm_num
private theorem prime_t29_5 : Nat.Prime 5 := by norm_num
private theorem prime_t29_7 : Nat.Prime 7 := by norm_num
private theorem prime_t29_11 : Nat.Prime 11 := by norm_num
private theorem prime_t29_13 : Nat.Prime 13 := by norm_num
private theorem prime_t29_17 : Nat.Prime 17 := by norm_num
private theorem prime_t29_19 : Nat.Prime 19 := by norm_num
private theorem prime_t29_23 : Nat.Prime 23 := by norm_num
private theorem prime_t29_29 : Nat.Prime 29 := by norm_num
private theorem prime_t29_31 : Nat.Prime 31 := by norm_num
private theorem prime_t29_37 : Nat.Prime 37 := by norm_num
private theorem prime_t29_41 : Nat.Prime 41 := by norm_num
private theorem prime_t29_43 : Nat.Prime 43 := by norm_num
private theorem prime_t29_47 : Nat.Prime 47 := by norm_num
private theorem prime_t29_53 : Nat.Prime 53 := by norm_num
private theorem prime_t29_59 : Nat.Prime 59 := by norm_num
private theorem prime_t29_61 : Nat.Prime 61 := by norm_num
private theorem prime_t29_71 : Nat.Prime 71 := by norm_num
private theorem prime_t29_73 : Nat.Prime 73 := by norm_num
private theorem prime_t29_79 : Nat.Prime 79 := by norm_num
private theorem prime_t29_83 : Nat.Prime 83 := by norm_num
private theorem prime_t29_89 : Nat.Prime 89 := by norm_num
private theorem prime_t29_101 : Nat.Prime 101 := by norm_num
private theorem prime_t29_107 : Nat.Prime 107 := by norm_num
private theorem prime_t29_131 : Nat.Prime 131 := by norm_num
private theorem prime_t29_149 : Nat.Prime 149 := by norm_num
private theorem prime_t29_151 : Nat.Prime 151 := by norm_num
private theorem prime_t29_193 : Nat.Prime 193 := by norm_num
private theorem prime_t29_197 : Nat.Prime 197 := by norm_num
private theorem prime_t29_241 : Nat.Prime 241 := by norm_num
private theorem prime_t29_263 : Nat.Prime 263 := by norm_num
private theorem prime_t29_271 : Nat.Prime 271 := by norm_num
private theorem prime_t29_311 : Nat.Prime 311 := by norm_num
private theorem prime_t29_331 : Nat.Prime 331 := by norm_num
private theorem prime_t29_337 : Nat.Prime 337 := by norm_num
private theorem prime_t29_349 : Nat.Prime 349 := by norm_num
private theorem prime_t29_379 : Nat.Prime 379 := by norm_num
private theorem prime_t29_443 : Nat.Prime 443 := by norm_num
private theorem prime_t29_461 : Nat.Prime 461 := by norm_num
private theorem prime_t29_641 : Nat.Prime 641 := by norm_num
private theorem prime_t29_659 : Nat.Prime 659 := by norm_num
private theorem prime_t29_761 : Nat.Prime 761 := by norm_num
private theorem prime_t29_797 : Nat.Prime 797 := by norm_num
private theorem prime_t29_983 : Nat.Prime 983 := by norm_num
private theorem prime_t29_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_t29_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_t29_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_t29_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_t29_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_t29_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_t29_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_t29_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_t29_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_t29_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_t29_3299 : Nat.Prime 3299 := by norm_num
private theorem prime_t29_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_t29_5273 : Nat.Prime 5273 := by norm_num
private theorem prime_t29_5827 : Nat.Prime 5827 := by norm_num
private theorem prime_t29_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_t29_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_t29_6779 : Nat.Prime 6779 := by norm_num
private theorem prime_t29_7717 : Nat.Prime 7717 := by norm_num
private theorem prime_t29_7789 : Nat.Prime 7789 := by norm_num
private theorem prime_t29_8581 : Nat.Prime 8581 := by norm_num
private theorem prime_t29_9649 : Nat.Prime 9649 := by norm_num
private theorem prime_t29_11239 : Nat.Prime 11239 := by norm_num
private theorem prime_t29_11933 : Nat.Prime 11933 := by norm_num
private theorem prime_t29_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_t29_20921 : Nat.Prime 20921 := by norm_num
private theorem prime_t29_21589 : Nat.Prime 21589 := by norm_num
private theorem prime_t29_27631 : Nat.Prime 27631 := by norm_num
private theorem prime_t29_27983 : Nat.Prime 27983 := by norm_num
private theorem prime_t29_28591 : Nat.Prime 28591 := by norm_num
private theorem prime_t29_28813 : Nat.Prime 28813 := by norm_num
private theorem prime_t29_29131 : Nat.Prime 29131 := by norm_num
private theorem prime_t29_34849 : Nat.Prime 34849 := by norm_num
private theorem prime_t29_36821 : Nat.Prime 36821 := by norm_num
private theorem prime_t29_46091 : Nat.Prime 46091 := by norm_num
private theorem prime_t29_58313 : Nat.Prime 58313 := by norm_num
private theorem prime_t29_59443 : Nat.Prime 59443 := by norm_num
private theorem prime_t29_65099 : Nat.Prime 65099 := by norm_num
private theorem prime_t29_77249 : Nat.Prime 77249 := by norm_num
private theorem prime_t29_82223 : Nat.Prime 82223 := by norm_num
private theorem prime_t29_83059 : Nat.Prime 83059 := by norm_num
private theorem prime_t29_220543 : Nat.Prime 220543 := by norm_num
private theorem prime_t29_229093 : Nat.Prime 229093 := by norm_num
private theorem prime_t29_262877 : Nat.Prime 262877 := by norm_num
private theorem prime_t29_333071 : Nat.Prime 333071 := by norm_num
private theorem prime_t29_384757 : Nat.Prime 384757 := by norm_num
private theorem prime_t29_388253 : Nat.Prime 388253 := by norm_num
private theorem prime_t29_577177 : Nat.Prime 577177 := by norm_num
private theorem prime_t29_582731 : Nat.Prime 582731 := by norm_num
private theorem prime_t29_765581 : Nat.Prime 765581 := by norm_num
private theorem prime_t29_1007549 : Nat.Prime 1007549 := by norm_num
private theorem prime_t29_1050367 : Nat.Prime 1050367 := by norm_num
private theorem prime_t29_1109477 : Nat.Prime 1109477 := by norm_num
private theorem prime_t29_1239737 : Nat.Prime 1239737 := by norm_num
private theorem prime_t29_1518949 : Nat.Prime 1518949 := by norm_num
private theorem prime_t29_1642211 : Nat.Prime 1642211 := by norm_num
private theorem prime_t29_1797413 : Nat.Prime 1797413 := by norm_num
private theorem prime_t29_2798707 : Nat.Prime 2798707 := by norm_num
private theorem prime_t29_3153587 : Nat.Prime 3153587 := by norm_num
private theorem prime_t29_3757393 : Nat.Prime 3757393 := by norm_num
private theorem prime_t29_4434811 : Nat.Prime 4434811 := by norm_num
private theorem prime_t29_4812611 : Nat.Prime 4812611 := by norm_num
private theorem prime_t29_8621819 : Nat.Prime 8621819 := by norm_num
private theorem prime_t29_9698761 : Nat.Prime 9698761 := by norm_num
private theorem prime_t29_11960917 : Nat.Prime 11960917 := by norm_num
private theorem prime_t29_17767171 : Nat.Prime 17767171 := by norm_num
private theorem prime_t29_29663129 : Nat.Prime 29663129 := by norm_num

/-! ## Exact t=29 window totients -/

private theorem phi_t29_2329089562801 : Nat.totient 2329089562801 = 2296463400000 := by
  rw [← show ((([(101, 1), (271, 1), (2311, 1), (36821, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_101, prime_t29_271, prime_t29_2311, prime_t29_36821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562802 : Nat.totient 2329089562802 = 1163977538832 := by
  rw [← show ((([(2, 1), (2053, 1), (567240517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_2053, prime_lucas_567240517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562803 : Nat.totient 2329089562803 = 1552060984320 := by
  rw [← show ((([(3, 1), (4159, 1), (6529, 1), (28591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_4159, prime_t29_6529, prime_t29_28591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562804 : Nat.totient 2329089562804 = 1160800263800 := by
  rw [← show ((([(2, 2), (311, 1), (1872258491, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_311, prime_lucas_1872258491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562805 : Nat.totient 2329089562805 = 1863078506496 := by
  rw [← show ((([(5, 1), (9649, 1), (48276289, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_5, prime_t29_9649, prime_lucas_48276289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562806 : Nat.totient 2329089562806 = 776363187600 := by
  rw [← show ((([(2, 1), (3, 1), (388181593801, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_lucas_388181593801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562807 : Nat.totient 2329089562807 = 1953886684632 := by
  rw [← show ((([(7, 1), (47, 1), (7079299583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_7, prime_t29_47, prime_lucas_7079299583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562808 : Nat.totient 2329089562808 = 1164393844128 := by
  rw [← show ((([(2, 3), (7717, 1), (37726603, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_7717, prime_lucas_37726603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562809 : Nat.totient 2329089562809 = 1552726375200 := by
  rw [← show ((([(3, 2), (258787729201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_lucas_258787729201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562810 : Nat.totient 2329089562810 = 931635825120 := by
  rw [← show ((([(2, 1), (5, 1), (232908956281, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_5, prime_lucas_232908956281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562811 : Nat.totient 2329089562811 = 2048748103200 := by
  rw [← show ((([(11, 1), (31, 1), (6779, 1), (1007549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_11, prime_t29_31, prime_t29_6779, prime_t29_1007549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562812 : Nat.totient 2329089562812 = 776359524400 := by
  rw [← show ((([(2, 2), (3, 1), (333071, 1), (582731, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_333071, prime_t29_582731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562813 : Nat.totient 2329089562813 = 2136101937984 := by
  rw [← show ((([(13, 1), (263, 1), (379, 1), (1797413, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_13, prime_t29_263, prime_t29_379, prime_t29_1797413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562814 : Nat.totient 2329089562814 = 998164092312 := by
  rw [← show ((([(2, 1), (7, 1), (59443, 1), (2798707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_7, prime_t29_59443, prime_t29_2798707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562815 : Nat.totient 2329089562815 = 1221019314816 := by
  rw [← show ((([(3, 1), (5, 1), (59, 1), (11933, 1), (220543, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_5, prime_t29_59, prime_t29_11933, prime_t29_220543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562816 : Nat.totient 2329089562816 = 1164544781376 := by
  rw [← show ((([(2, 6), (36392024419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_lucas_36392024419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562817 : Nat.totient 2329089562817 = 2180726341632 := by
  rw [← show ((([(17, 1), (193, 1), (709871857, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_17, prime_t29_193, prime_lucas_709871857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562818 : Nat.totient 2329089562818 = 776363187600 := by
  rw [← show ((([(2, 1), (3, 2), (129393864601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_lucas_129393864601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562819 : Nat.totient 2329089562819 = 2203063603200 := by
  rw [← show ((([(19, 1), (641, 1), (191238161, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_19, prime_t29_641, prime_lucas_191238161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562820 : Nat.totient 2329089562820 = 931635825120 := by
  rw [← show ((([(2, 2), (5, 1), (116454478141, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_5, prime_lucas_116454478141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562821 : Nat.totient 2329089562821 = 1312676699904 := by
  rw [← show ((([(3, 1), (7, 1), (73, 1), (1519301737, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_7, prime_t29_73, prime_lucas_1519301737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562822 : Nat.totient 2329089562822 = 1021598128320 := by
  rw [← show ((([(2, 1), (11, 1), (43, 1), (83, 1), (29663129, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_11, prime_t29_43, prime_t29_83, prime_t29_29663129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562823 : Nat.totient 2329089562823 = 2174694762240 := by
  rw [← show ((([(23, 1), (53, 1), (197, 1), (9698761, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_23, prime_t29_53, prime_t29_197, prime_t29_9698761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562824 : Nat.totient 2329089562824 = 770878085376 := by
  rw [← show ((([(2, 3), (3, 1), (149, 1), (2843, 1), (229093, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_149, prime_t29_2843, prime_t29_229093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562825 : Nat.totient 2329089562825 = 1863032276160 := by
  rw [← show ((([(5, 2), (7789, 1), (11960917, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_5, prime_t29_7789, prime_t29_11960917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562826 : Nat.totient 2329089562826 = 1074964413600 := by
  rw [← show ((([(2, 1), (13, 1), (89580367801, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_13, prime_lucas_89580367801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562827 : Nat.totient 2329089562827 = 1552726375200 := by
  rw [← show ((([(3, 3), (86262576401, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_lucas_86262576401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562828 : Nat.totient 2329089562828 = 973648143360 := by
  rw [← show ((([(2, 2), (7, 1), (41, 1), (5273, 1), (384757, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_7, prime_t29_41, prime_t29_5273, prime_t29_384757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562829 : Nat.totient 2329089562829 = 2241678922560 := by
  rw [← show ((([(29, 1), (331, 1), (11239, 1), (21589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_29, prime_t29_331, prime_t29_11239, prime_t29_21589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562830 : Nat.totient 2329089562830 = 621090550080 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (77636318761, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_5, prime_lucas_77636318761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562831 : Nat.totient 2329089562831 = 2266110675360 := by
  rw [← show ((([(37, 1), (82223, 1), (765581, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_37, prime_t29_82223, prime_t29_765581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562832 : Nat.totient 2329089562832 = 1133284431360 := by
  rw [← show ((([(2, 4), (61, 1), (107, 1), (797, 1), (27983, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_61, prime_t29_107, prime_t29_797, prime_t29_27983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562833 : Nat.totient 2329089562833 = 1411534164480 := by
  rw [← show ((([(3, 1), (11, 2), (77249, 1), (83059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_11, prime_t29_77249, prime_t29_83059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562834 : Nat.totient 2329089562834 = 1096042147200 := by
  rw [← show ((([(2, 1), (17, 1), (68502634201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_17, prime_lucas_68502634201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562835 : Nat.totient 2329089562835 = 1576873655136 := by
  rw [← show ((([(5, 1), (7, 1), (79, 1), (842347039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_5, prime_t29_7, prime_t29_79, prime_lucas_842347039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562836 : Nat.totient 2329089562836 = 776349174144 := by
  rw [← show ((([(2, 2), (3, 2), (58313, 1), (1109477, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_58313, prime_t29_1109477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562837 : Nat.totient 2329089562837 = 2319706193920 := by
  rw [← show ((([(461, 1), (1217, 1), (1433, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_461, prime_t29_1217, prime_t29_1433, prime_t29_2897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562838 : Nat.totient 2329089562838 = 1103252950800 := by
  rw [← show ((([(2, 1), (19, 1), (61291830601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_19, prime_lucas_61291830601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562839 : Nat.totient 2329089562839 = 1431827788128 := by
  rw [← show ((([(3, 1), (13, 1), (983, 1), (60753047, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_13, prime_t29_983, prime_lucas_60753047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562840 : Nat.totient 2329089562840 = 924524099200 := by
  rw [← show ((([(2, 3), (5, 1), (131, 1), (444482741, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_5, prime_t29_131, prime_lucas_444482741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562841 : Nat.totient 2329089562841 = 2312371587600 := by
  rw [← show ((([(151, 1), (1789, 1), (8621819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_151, prime_t29_1789, prime_t29_8621819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562842 : Nat.totient 2329089562842 = 643987895040 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (31, 1), (255550753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_7, prime_t29_31, prime_lucas_255550753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562843 : Nat.totient 2329089562843 = 2329089562842 := by
  rw [← show ((([(2329089562843, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_2329089562843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562844 : Nat.totient 2329089562844 = 1058645998080 := by
  rw [← show ((([(2, 2), (11, 1), (34849, 1), (1518949, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_11, prime_t29_34849, prime_t29_1518949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_2329089562845 : Nat.totient 2329089562845 = 1236632855040 := by
  rw [← show ((([(3, 2), (5, 1), (241, 1), (3299, 1), (65099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329089562845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_5, prime_t29_241, prime_t29_3299, prime_t29_65099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125601 : Nat.totient 4658179125601 = 4547913997200 := by
  rw [← show ((([(43, 1), (2351, 1), (46078157, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_43, prime_t29_2351, prime_lucas_46078157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125602 : Nat.totient 4658179125602 = 2296463400000 := by
  rw [← show ((([(2, 1), (101, 1), (271, 1), (2311, 1), (36821, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_101, prime_t29_271, prime_t29_2311, prime_t29_36821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125603 : Nat.totient 4658179125603 = 3054543688800 := by
  rw [← show ((([(3, 1), (61, 1), (25454530741, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_61, prime_lucas_25454530741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125604 : Nat.totient 4658179125604 = 2327955077664 := by
  rw [← show ((([(2, 2), (2053, 1), (567240517, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_2053, prime_lucas_567240517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125605 : Nat.totient 4658179125605 = 3720888452176 := by
  rw [← show ((([(5, 1), (659, 1), (1413711419, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_5, prime_t29_659, prime_lucas_1413711419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125606 : Nat.totient 4658179125606 = 1552060984320 := by
  rw [← show ((([(2, 1), (3, 1), (4159, 1), (6529, 1), (28591, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_4159, prime_t29_6529, prime_t29_28591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125607 : Nat.totient 4658179125607 = 3992724964800 := by
  rw [← show ((([(7, 1), (665454160801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_7, prime_lucas_665454160801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125608 : Nat.totient 4658179125608 = 2321600527600 := by
  rw [← show ((([(2, 3), (311, 1), (1872258491, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_311, prime_lucas_1872258491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125609 : Nat.totient 4658179125609 = 3105345972600 := by
  rw [← show ((([(3, 2), (29131, 1), (17767171, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_29131, prime_t29_17767171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125610 : Nat.totient 4658179125610 = 1863078506496 := by
  rw [← show ((([(2, 1), (5, 1), (9649, 1), (48276289, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_5, prime_t29_9649, prime_lucas_48276289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125611 : Nat.totient 4658179125611 = 4187127303040 := by
  rw [← show ((([(11, 1), (89, 1), (4758099209, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_11, prime_t29_89, prime_lucas_4758099209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125612 : Nat.totient 4658179125612 = 1552726375200 := by
  rw [← show ((([(2, 2), (3, 1), (388181593801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_lucas_388181593801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125613 : Nat.totient 4658179125613 = 4299857654400 := by
  rw [← show ((([(13, 1), (358321471201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_13, prime_lucas_358321471201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125614 : Nat.totient 4658179125614 = 1953886684632 := by
  rw [← show ((([(2, 1), (7, 1), (47, 1), (7079299583, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_7, prime_t29_47, prime_lucas_7079299583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125615 : Nat.totient 4658179125615 = 2423674659840 := by
  rw [← show ((([(3, 1), (5, 1), (41, 1), (28813, 1), (262877, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_5, prime_t29_41, prime_t29_28813, prime_t29_262877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125616 : Nat.totient 4658179125616 = 2328787688256 := by
  rw [← show ((([(2, 4), (7717, 1), (37726603, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_7717, prime_lucas_37726603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125617 : Nat.totient 4658179125617 = 4384168588800 := by
  rw [← show ((([(17, 1), (274010536801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_17, prime_lucas_274010536801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125618 : Nat.totient 4658179125618 = 1552726375200 := by
  rw [← show ((([(2, 1), (3, 2), (258787729201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_lucas_258787729201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125619 : Nat.totient 4658179125619 = 4389982047360 := by
  rw [← show ((([(19, 1), (337, 1), (443, 1), (1642211, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_19, prime_t29_337, prime_t29_443, prime_t29_1642211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125620 : Nat.totient 4658179125620 = 1863271650240 := by
  rw [← show ((([(2, 2), (5, 1), (232908956281, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_5, prime_lucas_232908956281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125621 : Nat.totient 4658179125621 = 2661758338800 := by
  rw [← show ((([(3, 1), (7, 1), (46091, 1), (4812611, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_7, prime_t29_46091, prime_t29_4812611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125622 : Nat.totient 4658179125622 = 2048748103200 := by
  rw [← show ((([(2, 1), (11, 1), (31, 1), (6779, 1), (1007549, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_11, prime_t29_31, prime_t29_6779, prime_t29_1007549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125623 : Nat.totient 4658179125623 = 4449232128000 := by
  rw [← show ((([(23, 1), (761, 1), (12721, 1), (20921, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_23, prime_t29_761, prime_t29_12721, prime_t29_20921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125624 : Nat.totient 4658179125624 = 1552719048800 := by
  rw [← show ((([(2, 3), (3, 1), (333071, 1), (582731, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_333071, prime_t29_582731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125625 : Nat.totient 4658179125625 = 3615430464000 := by
  rw [← show ((([(5, 4), (37, 1), (349, 1), (577177, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_5, prime_t29_37, prime_t29_349, prime_t29_577177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125626 : Nat.totient 4658179125626 = 2136101937984 := by
  rw [← show ((([(2, 1), (13, 1), (263, 1), (379, 1), (1797413, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_13, prime_t29_263, prime_t29_379, prime_t29_1797413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125627 : Nat.totient 4658179125627 = 3103585280784 := by
  rw [← show ((([(3, 4), (1663, 1), (34581109, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_1663, prime_lucas_34581109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125628 : Nat.totient 4658179125628 = 1996328184624 := by
  rw [← show ((([(2, 2), (7, 1), (59443, 1), (2798707, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_7, prime_t29_59443, prime_t29_2798707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125629 : Nat.totient 4658179125629 = 4433434057920 := by
  rw [← show ((([(29, 1), (71, 1), (5827, 1), (388253, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_29, prime_t29_71, prime_t29_5827, prime_t29_388253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125630 : Nat.totient 4658179125630 = 1221019314816 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (59, 1), (11933, 1), (220543, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_5, prime_t29_59, prime_t29_11933, prime_t29_220543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125631 : Nat.totient 4658179125631 = 4657636269000 := by
  rw [← show ((([(8581, 1), (542848051, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_8581, prime_lucas_542848051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125632 : Nat.totient 4658179125632 = 2329089562752 := by
  rw [← show ((([(2, 7), (36392024419, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_lucas_36392024419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125633 : Nat.totient 4658179125633 = 2820727962000 := by
  rw [← show ((([(3, 1), (11, 1), (1171, 1), (120543931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_11, prime_t29_1171, prime_lucas_120543931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125634 : Nat.totient 4658179125634 = 2180726341632 := by
  rw [← show ((([(2, 1), (17, 1), (193, 1), (709871857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_17, prime_t29_193, prime_lucas_709871857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125635 : Nat.totient 4658179125635 = 3193649156544 := by
  rw [← show ((([(5, 1), (7, 2), (6029, 1), (3153587, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_5, prime_t29_7, prime_t29_6029, prime_t29_3153587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125636 : Nat.totient 4658179125636 = 1552726375200 := by
  rw [← show ((([(2, 2), (3, 2), (129393864601, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_lucas_129393864601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125637 : Nat.totient 4658179125637 = 4658173640460 := by
  rw [← show ((([(1050367, 1), (4434811, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_1050367, prime_t29_4434811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125638 : Nat.totient 4658179125638 = 2203063603200 := by
  rw [← show ((([(2, 1), (19, 1), (641, 1), (191238161, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_19, prime_t29_641, prime_lucas_191238161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125639 : Nat.totient 4658179125639 = 2866571769600 := by
  rw [← show ((([(3, 1), (13, 1), (119440490401, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_13, prime_lucas_119440490401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125640 : Nat.totient 4658179125640 = 1863271650240 := by
  rw [← show ((([(2, 3), (5, 1), (116454478141, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_5, prime_lucas_116454478141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125641 : Nat.totient 4658179125641 = 4658174128512 := by
  rw [← show ((([(1239737, 1), (3757393, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_1239737, prime_t29_3757393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125642 : Nat.totient 4658179125642 = 1312676699904 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (73, 1), (1519301737, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_3, prime_t29_7, prime_t29_73, prime_lucas_1519301737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125643 : Nat.totient 4658179125643 = 4658010512760 := by
  rw [← show ((([(27631, 1), (168585253, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_27631, prime_lucas_168585253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125644 : Nat.totient 4658179125644 = 2043196256640 := by
  rw [← show ((([(2, 2), (11, 1), (43, 1), (83, 1), (29663129, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_2, prime_t29_11, prime_t29_43, prime_t29_83, prime_t29_29663129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t29_4658179125645 : Nat.totient 4658179125645 = 2484362200320 := by
  rw [← show ((([(3, 2), (5, 1), (103515091681, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658179125645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t29_3, prime_t29_5, prime_lucas_103515091681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The seventeenth finite diagonal certificate -/

theorem certifiedKill_diagonal_t29 :
    certifiedKill (periodLcm 29) (periodLcm 29) 45 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t29_2329089562801, phi_t29_2329089562802, phi_t29_2329089562803, phi_t29_2329089562804, phi_t29_2329089562805, phi_t29_2329089562806, phi_t29_2329089562807, phi_t29_2329089562808, phi_t29_2329089562809, phi_t29_2329089562810, phi_t29_2329089562811, phi_t29_2329089562812, phi_t29_2329089562813, phi_t29_2329089562814, phi_t29_2329089562815, phi_t29_2329089562816, phi_t29_2329089562817, phi_t29_2329089562818, phi_t29_2329089562819, phi_t29_2329089562820, phi_t29_2329089562821, phi_t29_2329089562822, phi_t29_2329089562823, phi_t29_2329089562824, phi_t29_2329089562825, phi_t29_2329089562826, phi_t29_2329089562827, phi_t29_2329089562828, phi_t29_2329089562829, phi_t29_2329089562830, phi_t29_2329089562831, phi_t29_2329089562832, phi_t29_2329089562833, phi_t29_2329089562834, phi_t29_2329089562835, phi_t29_2329089562836, phi_t29_2329089562837, phi_t29_2329089562838, phi_t29_2329089562839, phi_t29_2329089562840, phi_t29_2329089562841, phi_t29_2329089562842, phi_t29_2329089562843, phi_t29_2329089562844, phi_t29_2329089562845, phi_t29_4658179125601, phi_t29_4658179125602, phi_t29_4658179125603, phi_t29_4658179125604, phi_t29_4658179125605, phi_t29_4658179125606, phi_t29_4658179125607, phi_t29_4658179125608, phi_t29_4658179125609, phi_t29_4658179125610, phi_t29_4658179125611, phi_t29_4658179125612, phi_t29_4658179125613, phi_t29_4658179125614, phi_t29_4658179125615, phi_t29_4658179125616, phi_t29_4658179125617, phi_t29_4658179125618, phi_t29_4658179125619, phi_t29_4658179125620, phi_t29_4658179125621, phi_t29_4658179125622, phi_t29_4658179125623, phi_t29_4658179125624, phi_t29_4658179125625, phi_t29_4658179125626, phi_t29_4658179125627, phi_t29_4658179125628, phi_t29_4658179125629, phi_t29_4658179125630, phi_t29_4658179125631, phi_t29_4658179125632, phi_t29_4658179125633, phi_t29_4658179125634, phi_t29_4658179125635, phi_t29_4658179125636, phi_t29_4658179125637, phi_t29_4658179125638, phi_t29_4658179125639, phi_t29_4658179125640, phi_t29_4658179125641, phi_t29_4658179125642, phi_t29_4658179125643, phi_t29_4658179125644, phi_t29_4658179125645]

def diagonalPincerCertificateScalesThroughT29 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29]

def diagonalPincerKillDepthThroughT29 : ℕ → ℕ
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
  | _ => 0

/-- All 17 imported scales through t=29 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t29 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT29,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT29 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT29, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT29] using certifiedKill_diagonal_t29

#print axioms certifiedKill_diagonal_all_imported_through_t29

end TotientTailPeriodKiller
end Erdos249257
