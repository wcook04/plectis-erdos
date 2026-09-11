import Erdos249257.DiagonalPincerCertificatesT25
import Erdos249257.DiagonalPincerPrimeCertificates.Prime78354569
import Erdos249257.DiagonalPincerPrimeCertificates.Prime88891459
import Erdos249257.DiagonalPincerPrimeCertificates.Prime101086763
import Erdos249257.DiagonalPincerPrimeCertificates.Prime143033719
import Erdos249257.DiagonalPincerPrimeCertificates.Prime627448697
import Erdos249257.DiagonalPincerPrimeCertificates.Prime887441251
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1361244631
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2362159801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3030695593
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4015671661
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5019589577
import Erdos249257.DiagonalPincerPrimeCertificates.Prime6177956401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime8454045601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime16062686641
import Erdos249257.DiagonalPincerPrimeCertificates.Prime20078358301
import Erdos249257.DiagonalPincerPrimeCertificates.Prime32125373281
import Erdos249257.DiagonalPincerPrimeCertificates.Prime40156716601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime80313433231

/-!
# The t=27 diagonal-pincer certificate

This generated extension consumes 18 new large-prime Lucas roots
and 1 recursive Pratt dependency, reuses 12 earlier certificates,
reconstructs all 80 Euler totients in the t=27 window, and proves the
sixteenth finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=27 window -/

private theorem prime_t27_2 : Nat.Prime 2 := by norm_num
private theorem prime_t27_3 : Nat.Prime 3 := by norm_num
private theorem prime_t27_5 : Nat.Prime 5 := by norm_num
private theorem prime_t27_7 : Nat.Prime 7 := by norm_num
private theorem prime_t27_11 : Nat.Prime 11 := by norm_num
private theorem prime_t27_13 : Nat.Prime 13 := by norm_num
private theorem prime_t27_17 : Nat.Prime 17 := by norm_num
private theorem prime_t27_19 : Nat.Prime 19 := by norm_num
private theorem prime_t27_23 : Nat.Prime 23 := by norm_num
private theorem prime_t27_29 : Nat.Prime 29 := by norm_num
private theorem prime_t27_31 : Nat.Prime 31 := by norm_num
private theorem prime_t27_37 : Nat.Prime 37 := by norm_num
private theorem prime_t27_41 : Nat.Prime 41 := by norm_num
private theorem prime_t27_43 : Nat.Prime 43 := by norm_num
private theorem prime_t27_53 : Nat.Prime 53 := by norm_num
private theorem prime_t27_59 : Nat.Prime 59 := by norm_num
private theorem prime_t27_67 : Nat.Prime 67 := by norm_num
private theorem prime_t27_71 : Nat.Prime 71 := by norm_num
private theorem prime_t27_73 : Nat.Prime 73 := by norm_num
private theorem prime_t27_79 : Nat.Prime 79 := by norm_num
private theorem prime_t27_83 : Nat.Prime 83 := by norm_num
private theorem prime_t27_89 : Nat.Prime 89 := by norm_num
private theorem prime_t27_101 : Nat.Prime 101 := by norm_num
private theorem prime_t27_103 : Nat.Prime 103 := by norm_num
private theorem prime_t27_107 : Nat.Prime 107 := by norm_num
private theorem prime_t27_113 : Nat.Prime 113 := by norm_num
private theorem prime_t27_127 : Nat.Prime 127 := by norm_num
private theorem prime_t27_131 : Nat.Prime 131 := by norm_num
private theorem prime_t27_137 : Nat.Prime 137 := by norm_num
private theorem prime_t27_139 : Nat.Prime 139 := by norm_num
private theorem prime_t27_157 : Nat.Prime 157 := by norm_num
private theorem prime_t27_181 : Nat.Prime 181 := by norm_num
private theorem prime_t27_199 : Nat.Prime 199 := by norm_num
private theorem prime_t27_211 : Nat.Prime 211 := by norm_num
private theorem prime_t27_227 : Nat.Prime 227 := by norm_num
private theorem prime_t27_239 : Nat.Prime 239 := by norm_num
private theorem prime_t27_251 : Nat.Prime 251 := by norm_num
private theorem prime_t27_311 : Nat.Prime 311 := by norm_num
private theorem prime_t27_331 : Nat.Prime 331 := by norm_num
private theorem prime_t27_353 : Nat.Prime 353 := by norm_num
private theorem prime_t27_433 : Nat.Prime 433 := by norm_num
private theorem prime_t27_499 : Nat.Prime 499 := by norm_num
private theorem prime_t27_521 : Nat.Prime 521 := by norm_num
private theorem prime_t27_619 : Nat.Prime 619 := by norm_num
private theorem prime_t27_673 : Nat.Prime 673 := by norm_num
private theorem prime_t27_883 : Nat.Prime 883 := by norm_num
private theorem prime_t27_997 : Nat.Prime 997 := by norm_num
private theorem prime_t27_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_t27_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_t27_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_t27_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_t27_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_t27_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_t27_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_t27_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_t27_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_t27_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_t27_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_t27_4931 : Nat.Prime 4931 := by norm_num
private theorem prime_t27_5711 : Nat.Prime 5711 := by norm_num
private theorem prime_t27_5791 : Nat.Prime 5791 := by norm_num
private theorem prime_t27_5827 : Nat.Prime 5827 := by norm_num
private theorem prime_t27_5981 : Nat.Prime 5981 := by norm_num
private theorem prime_t27_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_t27_6719 : Nat.Prime 6719 := by norm_num
private theorem prime_t27_9629 : Nat.Prime 9629 := by norm_num
private theorem prime_t27_11239 : Nat.Prime 11239 := by norm_num
private theorem prime_t27_14303 : Nat.Prime 14303 := by norm_num
private theorem prime_t27_17569 : Nat.Prime 17569 := by norm_num
private theorem prime_t27_19891 : Nat.Prime 19891 := by norm_num
private theorem prime_t27_21589 : Nat.Prime 21589 := by norm_num
private theorem prime_t27_27791 : Nat.Prime 27791 := by norm_num
private theorem prime_t27_31019 : Nat.Prime 31019 := by norm_num
private theorem prime_t27_49331 : Nat.Prime 49331 := by norm_num
private theorem prime_t27_49697 : Nat.Prime 49697 := by norm_num
private theorem prime_t27_57731 : Nat.Prime 57731 := by norm_num
private theorem prime_t27_62969 : Nat.Prime 62969 := by norm_num
private theorem prime_t27_68071 : Nat.Prime 68071 := by norm_num
private theorem prime_t27_69767 : Nat.Prime 69767 := by norm_num
private theorem prime_t27_97577 : Nat.Prime 97577 := by norm_num
private theorem prime_t27_123419 : Nat.Prime 123419 := by norm_num
private theorem prime_t27_135671 : Nat.Prime 135671 := by norm_num
private theorem prime_t27_147481 : Nat.Prime 147481 := by norm_num
private theorem prime_t27_250267 : Nat.Prime 250267 := by norm_num
private theorem prime_t27_261431 : Nat.Prime 261431 := by norm_num
private theorem prime_t27_320911 : Nat.Prime 320911 := by norm_num
private theorem prime_t27_388253 : Nat.Prime 388253 := by norm_num
private theorem prime_t27_804059 : Nat.Prime 804059 := by norm_num
private theorem prime_t27_884899 : Nat.Prime 884899 := by norm_num
private theorem prime_t27_1347473 : Nat.Prime 1347473 := by norm_num
private theorem prime_t27_4728631 : Nat.Prime 4728631 := by norm_num
private theorem prime_t27_18578171 : Nat.Prime 18578171 := by norm_num
private theorem prime_t27_24322663 : Nat.Prime 24322663 := by norm_num
private theorem prime_t27_25597907 : Nat.Prime 25597907 := by norm_num
private theorem prime_t27_32003759 : Nat.Prime 32003759 := by norm_num

/-! ## Exact t=27 window totients -/

private theorem phi_t27_80313433201 : Nat.totient 80313433201 = 80059961520 := by
  rw [← show ((([(331, 1), (11239, 1), (21589, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_331, prime_t27_11239, prime_t27_21589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433202 : Nat.totient 80313433202 = 40156716600 := by
  rw [← show ((([(2, 1), (40156716601, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_lucas_40156716601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433203 : Nat.totient 80313433203 = 53542288800 := by
  rw [← show ((([(3, 1), (26771144401, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_lucas_26771144401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433204 : Nat.totient 80313433204 = 40156716600 := by
  rw [← show ((([(2, 2), (20078358301, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_lucas_20078358301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433205 : Nat.totient 80313433205 = 64250746560 := by
  rw [← show ((([(5, 1), (16062686641, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_5, prime_lucas_16062686641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433206 : Nat.totient 80313433206 = 26771144400 := by
  rw [← show ((([(2, 1), (3, 1), (13385572201, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_lucas_13385572201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433207 : Nat.totient 80313433207 = 68143140000 := by
  rw [← show ((([(7, 1), (101, 1), (5711, 1), (19891, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_7, prime_t27_101, prime_t27_5711, prime_t27_19891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433208 : Nat.totient 80313433208 = 40155854400 := by
  rw [← show ((([(2, 3), (68071, 1), (147481, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_68071, prime_t27_147481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433209 : Nat.totient 80313433209 = 53542288800 := by
  rw [← show ((([(3, 2), (8923714801, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_lucas_8923714801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433210 : Nat.totient 80313433210 = 29695610880 := by
  rw [← show ((([(2, 1), (5, 1), (31, 1), (37, 1), (103, 1), (157, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_5, prime_t27_31, prime_t27_37, prime_t27_103, prime_t27_157, prime_t27_433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433211 : Nat.totient 80313433211 = 72329013120 := by
  rw [← show ((([(11, 1), (113, 1), (2083, 1), (31019, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_11, prime_t27_113, prime_t27_2083, prime_t27_31019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433212 : Nat.totient 80313433212 = 26770404400 := by
  rw [← show ((([(2, 2), (3, 1), (49331, 1), (135671, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_t27_49331, prime_t27_135671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433213 : Nat.totient 80313433213 = 74135476800 := by
  rw [← show ((([(13, 1), (6177956401, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_13, prime_lucas_6177956401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433214 : Nat.totient 80313433214 = 34006376448 := by
  rw [← show ((([(2, 1), (7, 1), (89, 1), (1297, 1), (49697, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_7, prime_t27_89, prime_t27_1297, prime_t27_49697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433215 : Nat.totient 80313433215 = 42827345312 := by
  rw [← show ((([(3, 1), (5, 1), (6659, 1), (804059, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_5, prime_t27_6659, prime_t27_804059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433216 : Nat.totient 80313433216 = 40156716544 := by
  rw [← show ((([(2, 7), (627448697, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_lucas_627448697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433217 : Nat.totient 80313433217 = 75517715520 := by
  rw [← show ((([(17, 2), (1063, 1), (261431, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_17, prime_t27_1063, prime_t27_261431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433218 : Nat.totient 80313433218 = 26771144400 := by
  rw [← show ((([(2, 1), (3, 2), (4461857401, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_lucas_4461857401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433219 : Nat.totient 80313433219 = 76062099456 := by
  rw [← show ((([(19, 1), (3137, 1), (1347473, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_19, prime_t27_3137, prime_t27_1347473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433220 : Nat.totient 80313433220 = 32125373280 := by
  rw [← show ((([(2, 2), (5, 1), (4015671661, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_5, prime_lucas_4015671661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433221 : Nat.totient 80313433221 = 45893390400 := by
  rw [← show ((([(3, 1), (7, 1), (3824449201, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_7, prime_lucas_3824449201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433222 : Nat.totient 80313433222 = 36492234240 := by
  rw [← show ((([(2, 1), (11, 2), (2689, 1), (123419, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_11, prime_t27_2689, prime_t27_123419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433223 : Nat.totient 80313433223 = 73905511680 := by
  rw [← show ((([(23, 1), (43, 1), (79, 1), (521, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_23, prime_t27_43, prime_t27_79, prime_t27_521, prime_t27_1973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433224 : Nat.totient 80313433224 = 26674391040 := by
  rw [← show ((([(2, 3), (3, 1), (353, 1), (1637, 1), (5791, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_t27_353, prime_t27_1637, prime_t27_5791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433225 : Nat.totient 80313433225 = 62683654400 := by
  rw [← show ((([(5, 2), (41, 1), (78354569, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_5, prime_t27_41, prime_lucas_78354569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433226 : Nat.totient 80313433226 = 36775864944 := by
  rw [← show ((([(2, 1), (13, 1), (127, 1), (24322663, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_13, prime_t27_127, prime_t27_24322663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433227 : Nat.totient 80313433227 = 53542288764 := by
  rw [← show ((([(3, 4), (991523867, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_lucas_991523867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433228 : Nat.totient 80313433228 = 33222611520 := by
  rw [← show ((([(2, 2), (7, 1), (29, 1), (3559, 1), (27791, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_7, prime_t27_29, prime_t27_3559, prime_t27_27791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433229 : Nat.totient 80313433229 = 78952188540 := by
  rw [← show ((([(59, 1), (1361244631, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_59, prime_lucas_1361244631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433230 : Nat.totient 80313433230 = 21416915520 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (2677114441, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_t27_5, prime_lucas_2677114441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433231 : Nat.totient 80313433231 = 80313433230 := by
  rw [← show ((([(80313433231, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_80313433231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433232 : Nat.totient 80313433232 = 40156716608 := by
  rw [← show ((([(2, 4), (5019589577, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_lucas_5019589577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433233 : Nat.totient 80313433233 = 48303242000 := by
  rw [← show ((([(3, 1), (11, 1), (131, 1), (18578171, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_11, prime_t27_131, prime_t27_18578171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433234 : Nat.totient 80313433234 = 37794556800 := by
  rw [← show ((([(2, 1), (17, 1), (2362159801, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_17, prime_lucas_2362159801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433235 : Nat.totient 80313433235 = 54719400960 := by
  rw [← show ((([(5, 1), (7, 1), (211, 1), (619, 1), (17569, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_5, prime_t27_7, prime_t27_211, prime_t27_619, prime_t27_17569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433236 : Nat.totient 80313433236 = 26340773760 := by
  rw [← show ((([(2, 2), (3, 2), (71, 1), (499, 1), (62969, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_t27_71, prime_t27_499, prime_t27_62969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433237 : Nat.totient 80313433237 = 80312862060 := by
  rw [← show ((([(250267, 1), (320911, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_250267, prime_t27_320911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433238 : Nat.totient 80313433238 = 37657738080 := by
  rw [← show ((([(2, 1), (19, 1), (107, 1), (1381, 1), (14303, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_19, prime_t27_107, prime_t27_1381, prime_t27_14303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433239 : Nat.totient 80313433239 = 49423651200 := by
  rw [← show ((([(3, 1), (13, 1), (2059318801, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_13, prime_lucas_2059318801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_80313433240 : Nat.totient 80313433240 = 32111178624 := by
  rw [← show ((([(2, 3), (5, 1), (2269, 1), (884899, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313433240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_5, prime_t27_2269, prime_t27_884899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866401 : Nat.totient 160626866401 = 158336930640 := by
  rw [← show ((([(71, 1), (5827, 1), (388253, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_71, prime_t27_5827, prime_t27_388253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866402 : Nat.totient 160626866402 = 80059961520 := by
  rw [← show ((([(2, 1), (331, 1), (11239, 1), (21589, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_331, prime_t27_11239, prime_t27_21589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866403 : Nat.totient 160626866403 = 104594238504 := by
  rw [← show ((([(3, 1), (43, 1), (1245169507, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_43, prime_lucas_1245169507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866404 : Nat.totient 160626866404 = 80313433200 := by
  rw [← show ((([(2, 2), (40156716601, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_lucas_40156716601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866405 : Nat.totient 160626866405 = 128501493120 := by
  rw [← show ((([(5, 1), (32125373281, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_5, prime_lucas_32125373281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866406 : Nat.totient 160626866406 = 53542288800 := by
  rw [← show ((([(2, 1), (3, 1), (26771144401, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_lucas_26771144401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866407 : Nat.totient 160626866407 = 137073649272 := by
  rw [← show ((([(7, 1), (227, 1), (101086763, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_7, prime_t27_227, prime_lucas_101086763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866408 : Nat.totient 160626866408 = 80313433200 := by
  rw [← show ((([(2, 3), (20078358301, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_lucas_20078358301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866409 : Nat.totient 160626866409 = 102921062400 := by
  rw [← show ((([(3, 2), (41, 1), (73, 1), (997, 1), (5981, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_41, prime_t27_73, prime_t27_997, prime_t27_5981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866410 : Nat.totient 160626866410 = 64250746560 := by
  rw [← show ((([(2, 1), (5, 1), (16062686641, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_5, prime_lucas_16062686641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866411 : Nat.totient 160626866411 = 145336531200 := by
  rw [← show ((([(11, 1), (311, 1), (673, 1), (69767, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_11, prime_t27_311, prime_t27_673, prime_t27_69767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866412 : Nat.totient 160626866412 = 53542288800 := by
  rw [← show ((([(2, 2), (3, 1), (13385572201, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_lucas_13385572201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866413 : Nat.totient 160626866413 = 147204254448 := by
  rw [← show ((([(13, 1), (139, 1), (88891459, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_13, prime_t27_139, prime_lucas_88891459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866414 : Nat.totient 160626866414 = 68143140000 := by
  rw [← show ((([(2, 1), (7, 1), (101, 1), (5711, 1), (19891, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_7, prime_t27_101, prime_t27_5711, prime_t27_19891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866415 : Nat.totient 160626866415 = 85667662080 := by
  rw [← show ((([(3, 1), (5, 1), (10708457761, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_5, prime_lucas_10708457761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866416 : Nat.totient 160626866416 = 80311708800 := by
  rw [← show ((([(2, 4), (68071, 1), (147481, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_68071, prime_t27_147481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866417 : Nat.totient 160626866417 = 150372414720 := by
  rw [← show ((([(17, 1), (199, 1), (4931, 1), (9629, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_17, prime_t27_199, prime_t27_4931, prime_t27_9629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866418 : Nat.totient 160626866418 = 53542288800 := by
  rw [← show ((([(2, 1), (3, 2), (8923714801, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_lucas_8923714801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866419 : Nat.totient 160626866419 = 152172820800 := by
  rw [← show ((([(19, 1), (8454045601, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_19, prime_lucas_8454045601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866420 : Nat.totient 160626866420 = 59391221760 := by
  rw [← show ((([(2, 2), (5, 1), (31, 1), (37, 1), (103, 1), (157, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_5, prime_t27_31, prime_t27_37, prime_t27_103, prime_t27_157, prime_t27_433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866421 : Nat.totient 160626866421 = 91402732848 := by
  rw [← show ((([(3, 1), (7, 1), (239, 1), (32003759, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_7, prime_t27_239, prime_t27_32003759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866422 : Nat.totient 160626866422 = 72329013120 := by
  rw [← show ((([(2, 1), (11, 1), (113, 1), (2083, 1), (31019, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_11, prime_t27_113, prime_t27_2083, prime_t27_31019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866423 : Nat.totient 160626866423 = 152346237120 := by
  rw [← show ((([(23, 1), (137, 1), (883, 1), (57731, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_23, prime_t27_137, prime_t27_883, prime_t27_57731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866424 : Nat.totient 160626866424 = 53540808800 := by
  rw [← show ((([(2, 3), (3, 1), (49331, 1), (135671, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_t27_49331, prime_t27_135671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866425 : Nat.totient 160626866425 = 127989530000 := by
  rw [← show ((([(5, 2), (251, 1), (25597907, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_5, prime_t27_251, prime_t27_25597907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866426 : Nat.totient 160626866426 = 74135476800 := by
  rw [← show ((([(2, 1), (13, 1), (6177956401, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_13, prime_lucas_6177956401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866427 : Nat.totient 160626866427 = 103392005472 := by
  rw [← show ((([(3, 3), (29, 1), (205142869, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_29, prime_lucas_205142869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866428 : Nat.totient 160626866428 = 68012752896 := by
  rw [← show ((([(2, 2), (7, 1), (89, 1), (1297, 1), (49697, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_7, prime_t27_89, prime_t27_1297, prime_t27_49697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866429 : Nat.totient 160626866429 = 157596170784 := by
  rw [← show ((([(53, 1), (3030695593, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_53, prime_lucas_3030695593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866430 : Nat.totient 160626866430 = 42827345312 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (6659, 1), (804059, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_t27_5, prime_t27_6659, prime_t27_804059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866431 : Nat.totient 160626866431 = 159739425000 := by
  rw [← show ((([(181, 1), (887441251, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_181, prime_lucas_887441251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866432 : Nat.totient 160626866432 = 80313433088 := by
  rw [← show ((([(2, 8), (627448697, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_lucas_627448697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866433 : Nat.totient 160626866433 = 96176727440 := by
  rw [← show ((([(3, 1), (11, 1), (83, 1), (58644347, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_11, prime_t27_83, prime_lucas_58644347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866434 : Nat.totient 160626866434 = 75517715520 := by
  rw [← show ((([(2, 1), (17, 2), (1063, 1), (261431, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_17, prime_t27_1063, prime_t27_261431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866435 : Nat.totient 160626866435 = 110126615424 := by
  rw [← show ((([(5, 1), (7, 2), (6719, 1), (97577, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_5, prime_t27_7, prime_t27_6719, prime_t27_97577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866436 : Nat.totient 160626866436 = 53542288800 := by
  rw [← show ((([(2, 2), (3, 2), (4461857401, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_3, prime_lucas_4461857401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866437 : Nat.totient 160626866437 = 160483831596 := by
  rw [← show ((([(1123, 1), (143033719, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_1123, prime_lucas_143033719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866438 : Nat.totient 160626866438 = 76062099456 := by
  rw [← show ((([(2, 1), (19, 1), (3137, 1), (1347473, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_19, prime_t27_3137, prime_t27_1347473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866439 : Nat.totient 160626866439 = 97371948960 := by
  rw [← show ((([(3, 1), (13, 2), (67, 1), (4728631, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_3, prime_t27_13, prime_t27_67, prime_t27_4728631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t27_160626866440 : Nat.totient 160626866440 = 64250746560 := by
  rw [← show ((([(2, 3), (5, 1), (4015671661, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626866440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t27_2, prime_t27_5, prime_lucas_4015671661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The sixteenth finite diagonal certificate -/

theorem certifiedKill_diagonal_t27 :
    certifiedKill (periodLcm 27) (periodLcm 27) 40 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t27_80313433201, phi_t27_80313433202, phi_t27_80313433203, phi_t27_80313433204, phi_t27_80313433205, phi_t27_80313433206, phi_t27_80313433207, phi_t27_80313433208, phi_t27_80313433209, phi_t27_80313433210, phi_t27_80313433211, phi_t27_80313433212, phi_t27_80313433213, phi_t27_80313433214, phi_t27_80313433215, phi_t27_80313433216, phi_t27_80313433217, phi_t27_80313433218, phi_t27_80313433219, phi_t27_80313433220, phi_t27_80313433221, phi_t27_80313433222, phi_t27_80313433223, phi_t27_80313433224, phi_t27_80313433225, phi_t27_80313433226, phi_t27_80313433227, phi_t27_80313433228, phi_t27_80313433229, phi_t27_80313433230, phi_t27_80313433231, phi_t27_80313433232, phi_t27_80313433233, phi_t27_80313433234, phi_t27_80313433235, phi_t27_80313433236, phi_t27_80313433237, phi_t27_80313433238, phi_t27_80313433239, phi_t27_80313433240, phi_t27_160626866401, phi_t27_160626866402, phi_t27_160626866403, phi_t27_160626866404, phi_t27_160626866405, phi_t27_160626866406, phi_t27_160626866407, phi_t27_160626866408, phi_t27_160626866409, phi_t27_160626866410, phi_t27_160626866411, phi_t27_160626866412, phi_t27_160626866413, phi_t27_160626866414, phi_t27_160626866415, phi_t27_160626866416, phi_t27_160626866417, phi_t27_160626866418, phi_t27_160626866419, phi_t27_160626866420, phi_t27_160626866421, phi_t27_160626866422, phi_t27_160626866423, phi_t27_160626866424, phi_t27_160626866425, phi_t27_160626866426, phi_t27_160626866427, phi_t27_160626866428, phi_t27_160626866429, phi_t27_160626866430, phi_t27_160626866431, phi_t27_160626866432, phi_t27_160626866433, phi_t27_160626866434, phi_t27_160626866435, phi_t27_160626866436, phi_t27_160626866437, phi_t27_160626866438, phi_t27_160626866439, phi_t27_160626866440]

def diagonalPincerCertificateScalesThroughT27 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27]

def diagonalPincerKillDepthThroughT27 : ℕ → ℕ
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
  | _ => 0

/-- All 16 imported scales through t=27 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t27 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT27,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT27 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT27, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT27] using certifiedKill_diagonal_t27

#print axioms certifiedKill_diagonal_all_imported_through_t27

end TotientTailPeriodKiller
end Erdos249257
