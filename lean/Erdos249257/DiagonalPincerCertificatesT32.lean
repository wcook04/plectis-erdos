import Erdos249257.DiagonalPincerCertificatesT31
import Erdos249257.DiagonalPincerPrimeCertificates.Prime77178373
import Erdos249257.DiagonalPincerPrimeCertificates.Prime289946887
import Erdos249257.DiagonalPincerPrimeCertificates.Prime777012787
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1751057131
import Erdos249257.DiagonalPincerPrimeCertificates.Prime14474370059
import Erdos249257.DiagonalPincerPrimeCertificates.Prime262790815093
import Erdos249257.DiagonalPincerPrimeCertificates.Prime299903536643
import Erdos249257.DiagonalPincerPrimeCertificates.Prime426598383733
import Erdos249257.DiagonalPincerPrimeCertificates.Prime6417935684161
import Erdos249257.DiagonalPincerPrimeCertificates.Prime8251631593921
import Erdos249257.DiagonalPincerPrimeCertificates.Prime16988653281601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime57761421157441
import Erdos249257.DiagonalPincerPrimeCertificates.Prime288807105787247

/-!
# The t=32 diagonal-pincer certificate

This generated extension consumes 13 new large-prime Lucas roots
and 3 recursive Pratt dependencies, reuses 33 earlier certificates,
reconstructs all 100 Euler totients in the t=32 window, and proves the
nineteenth finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=32 window -/

private theorem prime_t32_2 : Nat.Prime 2 := by norm_num
private theorem prime_t32_3 : Nat.Prime 3 := by norm_num
private theorem prime_t32_5 : Nat.Prime 5 := by norm_num
private theorem prime_t32_7 : Nat.Prime 7 := by norm_num
private theorem prime_t32_11 : Nat.Prime 11 := by norm_num
private theorem prime_t32_13 : Nat.Prime 13 := by norm_num
private theorem prime_t32_17 : Nat.Prime 17 := by norm_num
private theorem prime_t32_19 : Nat.Prime 19 := by norm_num
private theorem prime_t32_23 : Nat.Prime 23 := by norm_num
private theorem prime_t32_29 : Nat.Prime 29 := by norm_num
private theorem prime_t32_31 : Nat.Prime 31 := by norm_num
private theorem prime_t32_37 : Nat.Prime 37 := by norm_num
private theorem prime_t32_41 : Nat.Prime 41 := by norm_num
private theorem prime_t32_43 : Nat.Prime 43 := by norm_num
private theorem prime_t32_47 : Nat.Prime 47 := by norm_num
private theorem prime_t32_53 : Nat.Prime 53 := by norm_num
private theorem prime_t32_59 : Nat.Prime 59 := by norm_num
private theorem prime_t32_61 : Nat.Prime 61 := by norm_num
private theorem prime_t32_67 : Nat.Prime 67 := by norm_num
private theorem prime_t32_71 : Nat.Prime 71 := by norm_num
private theorem prime_t32_73 : Nat.Prime 73 := by norm_num
private theorem prime_t32_79 : Nat.Prime 79 := by norm_num
private theorem prime_t32_83 : Nat.Prime 83 := by norm_num
private theorem prime_t32_97 : Nat.Prime 97 := by norm_num
private theorem prime_t32_101 : Nat.Prime 101 := by norm_num
private theorem prime_t32_103 : Nat.Prime 103 := by norm_num
private theorem prime_t32_107 : Nat.Prime 107 := by norm_num
private theorem prime_t32_109 : Nat.Prime 109 := by norm_num
private theorem prime_t32_113 : Nat.Prime 113 := by norm_num
private theorem prime_t32_127 : Nat.Prime 127 := by norm_num
private theorem prime_t32_139 : Nat.Prime 139 := by norm_num
private theorem prime_t32_157 : Nat.Prime 157 := by norm_num
private theorem prime_t32_163 : Nat.Prime 163 := by norm_num
private theorem prime_t32_197 : Nat.Prime 197 := by norm_num
private theorem prime_t32_241 : Nat.Prime 241 := by norm_num
private theorem prime_t32_251 : Nat.Prime 251 := by norm_num
private theorem prime_t32_257 : Nat.Prime 257 := by norm_num
private theorem prime_t32_263 : Nat.Prime 263 := by norm_num
private theorem prime_t32_277 : Nat.Prime 277 := by norm_num
private theorem prime_t32_293 : Nat.Prime 293 := by norm_num
private theorem prime_t32_313 : Nat.Prime 313 := by norm_num
private theorem prime_t32_379 : Nat.Prime 379 := by norm_num
private theorem prime_t32_397 : Nat.Prime 397 := by norm_num
private theorem prime_t32_421 : Nat.Prime 421 := by norm_num
private theorem prime_t32_433 : Nat.Prime 433 := by norm_num
private theorem prime_t32_479 : Nat.Prime 479 := by norm_num
private theorem prime_t32_563 : Nat.Prime 563 := by norm_num
private theorem prime_t32_661 : Nat.Prime 661 := by norm_num
private theorem prime_t32_677 : Nat.Prime 677 := by norm_num
private theorem prime_t32_739 : Nat.Prime 739 := by norm_num
private theorem prime_t32_827 : Nat.Prime 827 := by norm_num
private theorem prime_t32_971 : Nat.Prime 971 := by norm_num
private theorem prime_t32_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_t32_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_t32_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_t32_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_t32_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_t32_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_t32_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_t32_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_t32_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_t32_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_t32_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_t32_2129 : Nat.Prime 2129 := by norm_num
private theorem prime_t32_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_t32_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_t32_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_t32_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_t32_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_t32_5443 : Nat.Prime 5443 := by norm_num
private theorem prime_t32_6311 : Nat.Prime 6311 := by norm_num
private theorem prime_t32_6907 : Nat.Prime 6907 := by norm_num
private theorem prime_t32_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_t32_7331 : Nat.Prime 7331 := by norm_num
private theorem prime_t32_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_t32_9697 : Nat.Prime 9697 := by norm_num
private theorem prime_t32_10243 : Nat.Prime 10243 := by norm_num
private theorem prime_t32_12107 : Nat.Prime 12107 := by norm_num
private theorem prime_t32_13367 : Nat.Prime 13367 := by norm_num
private theorem prime_t32_14627 : Nat.Prime 14627 := by norm_num
private theorem prime_t32_14831 : Nat.Prime 14831 := by norm_num
private theorem prime_t32_15199 : Nat.Prime 15199 := by norm_num
private theorem prime_t32_16963 : Nat.Prime 16963 := by norm_num
private theorem prime_t32_18013 : Nat.Prime 18013 := by norm_num
private theorem prime_t32_18041 : Nat.Prime 18041 := by norm_num
private theorem prime_t32_24247 : Nat.Prime 24247 := by norm_num
private theorem prime_t32_25741 : Nat.Prime 25741 := by norm_num
private theorem prime_t32_26423 : Nat.Prime 26423 := by norm_num
private theorem prime_t32_33529 : Nat.Prime 33529 := by norm_num
private theorem prime_t32_57737 : Nat.Prime 57737 := by norm_num
private theorem prime_t32_65027 : Nat.Prime 65027 := by norm_num
private theorem prime_t32_116141 : Nat.Prime 116141 := by norm_num
private theorem prime_t32_129037 : Nat.Prime 129037 := by norm_num
private theorem prime_t32_139393 : Nat.Prime 139393 := by norm_num
private theorem prime_t32_178813 : Nat.Prime 178813 := by norm_num
private theorem prime_t32_301643 : Nat.Prime 301643 := by norm_num
private theorem prime_t32_330103 : Nat.Prime 330103 := by norm_num
private theorem prime_t32_340939 : Nat.Prime 340939 := by norm_num
private theorem prime_t32_437071 : Nat.Prime 437071 := by norm_num
private theorem prime_t32_464003 : Nat.Prime 464003 := by norm_num
private theorem prime_t32_535013 : Nat.Prime 535013 := by norm_num
private theorem prime_t32_575591 : Nat.Prime 575591 := by norm_num
private theorem prime_t32_870229 : Nat.Prime 870229 := by norm_num
private theorem prime_t32_974999 : Nat.Prime 974999 := by norm_num
private theorem prime_t32_1070869 : Nat.Prime 1070869 := by norm_num
private theorem prime_t32_1195361 : Nat.Prime 1195361 := by norm_num
private theorem prime_t32_1314011 : Nat.Prime 1314011 := by norm_num
private theorem prime_t32_1725259 : Nat.Prime 1725259 := by norm_num
private theorem prime_t32_1855093 : Nat.Prime 1855093 := by norm_num
private theorem prime_t32_1883503 : Nat.Prime 1883503 := by norm_num
private theorem prime_t32_2017567 : Nat.Prime 2017567 := by norm_num
private theorem prime_t32_2239889 : Nat.Prime 2239889 := by norm_num
private theorem prime_t32_3718417 : Nat.Prime 3718417 := by norm_num
private theorem prime_t32_3814439 : Nat.Prime 3814439 := by norm_num
private theorem prime_t32_5630201 : Nat.Prime 5630201 := by norm_num
private theorem prime_t32_6195041 : Nat.Prime 6195041 := by norm_num
private theorem prime_t32_6550651 : Nat.Prime 6550651 := by norm_num
private theorem prime_t32_7897873 : Nat.Prime 7897873 := by norm_num
private theorem prime_t32_8379187 : Nat.Prime 8379187 := by norm_num
private theorem prime_t32_9308753 : Nat.Prime 9308753 := by norm_num
private theorem prime_t32_12499271 : Nat.Prime 12499271 := by norm_num
private theorem prime_t32_16144279 : Nat.Prime 16144279 := by norm_num
private theorem prime_t32_18358229 : Nat.Prime 18358229 := by norm_num
private theorem prime_t32_21720121 : Nat.Prime 21720121 := by norm_num
private theorem prime_t32_22124989 : Nat.Prime 22124989 := by norm_num

/-! ## Exact t=32 window totients -/

private theorem phi_t32_144403552893601 : Nat.totient 144403552893601 = 144323373240000 := by
  rw [← show ((([(1801, 1), (80179651801, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_1801, prime_lucas_80179651801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893602 : Nat.totient 144403552893602 = 72201776446800 := by
  rw [← show ((([(2, 1), (72201776446801, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_lucas_72201776446801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893603 : Nat.totient 144403552893603 = 95415614985600 := by
  rw [← show ((([(3, 1), (113, 1), (65027, 1), (6550651, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_113, prime_t32_65027, prime_t32_6550651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893604 : Nat.totient 144403552893604 = 71535405553920 := by
  rw [← show ((([(2, 2), (109, 1), (18041, 1), (18358229, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_109, prime_t32_18041, prime_t32_18358229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893605 : Nat.totient 144403552893605 = 115521847172800 := by
  rw [← show ((([(5, 1), (116141, 1), (248669381, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_5, prime_t32_116141, prime_lucas_248669381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893606 : Nat.totient 144403552893606 = 48134517631200 := by
  rw [← show ((([(2, 1), (3, 1), (24067258815601, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_lucas_24067258815601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893607 : Nat.totient 144403552893607 = 123774473908764 := by
  rw [← show ((([(7, 2), (2947011283543, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_7, prime_lucas_2947011283543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893608 : Nat.totient 144403552893608 = 72201776446800 := by
  rw [← show ((([(2, 3), (18050444111701, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_lucas_18050444111701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893609 : Nat.totient 144403552893609 = 96237432225792 := by
  rw [← show ((([(3, 2), (3433, 1), (33529, 1), (139393, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_3433, prime_t32_33529, prime_t32_139393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893610 : Nat.totient 144403552893610 = 57761421157440 := by
  rw [← show ((([(2, 1), (5, 1), (14440355289361, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_lucas_14440355289361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893611 : Nat.totient 144403552893611 = 127558514578080 := by
  rw [← show ((([(11, 1), (47, 1), (139, 1), (2009428397, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_11, prime_t32_47, prime_t32_139, prime_lucas_2009428397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893612 : Nat.totient 144403552893612 = 47755505680848 := by
  rw [← show ((([(2, 2), (3, 1), (127, 1), (94752987463, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_127, prime_lucas_94752987463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893613 : Nat.totient 144403552893613 = 133295587286400 := by
  rw [← show ((([(13, 1), (11107965607201, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_13, prime_lucas_11107965607201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893614 : Nat.totient 144403552893614 = 60377549112000 := by
  rw [← show ((([(2, 1), (7, 1), (41, 1), (437071, 1), (575591, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_7, prime_t32_41, prime_t32_437071, prime_t32_575591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893615 : Nat.totient 144403552893615 = 76854444848672 := by
  rw [← show ((([(3, 1), (5, 1), (479, 1), (20097919679, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_5, prime_t32_479, prime_lucas_20097919679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893616 : Nat.totient 144403552893616 = 72201776446800 := by
  rw [← show ((([(2, 4), (9025222055851, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_lucas_9025222055851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893617 : Nat.totient 144403552893617 = 135301404157440 := by
  rw [← show ((([(17, 1), (263, 1), (1487, 1), (21720121, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_17, prime_t32_263, prime_t32_1487, prime_t32_21720121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893618 : Nat.totient 144403552893618 = 48012195924000 := by
  rw [← show ((([(2, 1), (3, 2), (661, 1), (971, 1), (12499271, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_661, prime_t32_971, prime_t32_12499271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893619 : Nat.totient 144403552893619 = 136772421832800 := by
  rw [← show ((([(19, 1), (4421, 1), (1719110381, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_19, prime_t32_4421, prime_lucas_1719110381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893620 : Nat.totient 144403552893620 = 56899310393376 := by
  rw [← show ((([(2, 2), (5, 1), (67, 1), (107763845443, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_t32_67, prime_lucas_107763845443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893621 : Nat.totient 144403552893621 = 82511734791744 := by
  rw [← show ((([(3, 1), (7, 1), (18013, 1), (381744277, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_7, prime_t32_18013, prime_lucas_381744277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893622 : Nat.totient 144403552893622 = 65637978588000 := by
  rw [← show ((([(2, 1), (11, 1), (6563797858801, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_11, prime_lucas_6563797858801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893623 : Nat.totient 144403552893623 = 138125137550400 := by
  rw [← show ((([(23, 1), (6278415343201, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_23, prime_lucas_6278415343201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893624 : Nat.totient 144403552893624 = 48107835278976 := by
  rw [← show ((([(2, 3), (3, 1), (2293, 1), (8699, 1), (301643, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_2293, prime_t32_8699, prime_t32_301643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893625 : Nat.totient 144403552893625 = 115522842314800 := by
  rw [← show ((([(5, 3), (1155228423149, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_5, prime_lucas_1155228423149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893626 : Nat.totient 144403552893626 = 66647793643200 := by
  rw [← show ((([(2, 1), (13, 1), (5553982803601, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_13, prime_lucas_5553982803601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893627 : Nat.totient 144403552893627 = 96269035262256 := by
  rw [← show ((([(3, 5), (594253304089, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_lucas_594253304089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893628 : Nat.totient 144403552893628 = 61739331868800 := by
  rw [← show ((([(2, 2), (7, 1), (563, 1), (1627, 1), (5630201, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_7, prime_t32_563, prime_t32_1627, prime_t32_5630201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893629 : Nat.totient 144403552893629 = 138967090604160 := by
  rw [← show ((([(29, 1), (313, 1), (12107, 1), (1314011, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_29, prime_t32_313, prime_t32_12107, prime_t32_1314011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893630 : Nat.totient 144403552893630 = 38507614104960 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (4813451763121, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_5, prime_lucas_4813451763121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893631 : Nat.totient 144403552893631 = 136437419916000 := by
  rw [← show ((([(31, 1), (43, 1), (2351, 1), (46078157, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_31, prime_t32_43, prime_t32_2351, prime_lucas_46078157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893632 : Nat.totient 144403552893632 = 71010798428160 := by
  rw [← show ((([(2, 6), (61, 1), (9697, 1), (3814439, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_61, prime_t32_9697, prime_t32_3814439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893633 : Nat.totient 144403552893633 = 87176770519040 := by
  rw [← show ((([(3, 1), (11, 1), (257, 1), (17026712993, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_11, prime_t32_257, prime_lucas_17026712993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893634 : Nat.totient 144403552893634 = 67945343521600 := by
  rw [← show ((([(2, 1), (17, 1), (7331, 1), (579342971, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_17, prime_t32_7331, prime_lucas_579342971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893635 : Nat.totient 144403552893635 = 96329419661952 := by
  rw [← show ((([(5, 1), (7, 1), (37, 1), (6907, 1), (16144279, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_5, prime_t32_7, prime_t32_37, prime_t32_6907, prime_t32_16144279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893636 : Nat.totient 144403552893636 = 47554583682864 := by
  rw [← show ((([(2, 2), (3, 2), (83, 1), (48327828947, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_83, prime_lucas_48327828947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893637 : Nat.totient 144403552893637 = 142575659818956 := by
  rw [← show ((([(79, 1), (1827893074603, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_79, prime_lucas_1827893074603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893638 : Nat.totient 144403552893638 = 68401612730376 := by
  rw [← show ((([(2, 1), (19, 1), (1883503, 1), (2017567, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_19, prime_t32_1883503, prime_t32_2017567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893639 : Nat.totient 144403552893639 = 88863724857600 := by
  rw [← show ((([(3, 1), (13, 1), (3702655202401, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_13, prime_lucas_3702655202401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893640 : Nat.totient 144403552893640 = 57548531551488 := by
  rw [← show ((([(2, 3), (5, 1), (277, 1), (13367, 1), (974999, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_t32_277, prime_t32_13367, prime_t32_974999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893641 : Nat.totient 144403552893641 = 144403552893640 := by
  rw [← show ((([(144403552893641, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_144403552893641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893642 : Nat.totient 144403552893642 = 41255375905200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (14831, 1), (231823871, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_7, prime_t32_14831, prime_lucas_231823871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893643 : Nat.totient 144403552893643 = 144403552893642 := by
  rw [← show ((([(144403552893643, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_144403552893643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893644 : Nat.totient 144403552893644 = 65469751364160 := by
  rw [← show ((([(2, 2), (11, 1), (397, 1), (24247, 1), (340939, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_11, prime_t32_397, prime_t32_24247, prime_t32_340939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893645 : Nat.totient 144403552893645 = 75704688963072 := by
  rw [← show ((([(3, 2), (5, 1), (59, 1), (14627, 1), (3718417, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_5, prime_t32_59, prime_t32_14627, prime_t32_3718417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893646 : Nat.totient 144403552893646 = 68826860342944 := by
  rw [← show ((([(2, 1), (23, 1), (293, 1), (10714019357, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_23, prime_t32_293, prime_lucas_10714019357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893647 : Nat.totient 144403552893647 = 141643765751040 := by
  rw [← show ((([(71, 1), (197, 1), (57737, 1), (178813, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_71, prime_t32_197, prime_t32_57737, prime_t32_178813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893648 : Nat.totient 144403552893648 = 46534820806656 := by
  rw [← show ((([(2, 4), (3, 1), (53, 1), (97, 1), (379, 1), (827, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_53, prime_t32_97, prime_t32_379, prime_t32_827, prime_t32_1867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893649 : Nat.totient 144403552893649 = 123774473908836 := by
  rw [← show ((([(7, 1), (20629078984807, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_7, prime_lucas_20629078984807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_144403552893650 : Nat.totient 144403552893650 = 57729874741200 := by
  rw [← show ((([(2, 1), (5, 2), (1831, 1), (1577318983, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_t32_1831, prime_lucas_1577318983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787201 : Nat.totient 288807105787201 = 288759754708272 := by
  rw [← show ((([(10243, 1), (15199, 1), (1855093, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_10243, prime_t32_15199, prime_t32_1855093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787202 : Nat.totient 288807105787202 = 144323373240000 := by
  rw [← show ((([(2, 1), (1801, 1), (80179651801, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_1801, prime_lucas_80179651801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787203 : Nat.totient 288807105787203 = 189346914433440 := by
  rw [← show ((([(3, 1), (61, 1), (5443, 1), (289946887, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_61, prime_t32_5443, prime_lucas_289946887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787204 : Nat.totient 288807105787204 = 144403552893600 := by
  rw [← show ((([(2, 2), (72201776446801, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_lucas_72201776446801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787205 : Nat.totient 288807105787205 = 231045684629760 := by
  rw [← show ((([(5, 1), (57761421157441, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_5, prime_lucas_57761421157441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787206 : Nat.totient 288807105787206 = 95415614985600 := by
  rw [← show ((([(2, 1), (3, 1), (113, 1), (65027, 1), (6550651, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_113, prime_t32_65027, prime_t32_6550651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787207 : Nat.totient 288807105787207 = 245972202926112 := by
  rw [← show ((([(7, 1), (157, 1), (262790815093, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_7, prime_t32_157, prime_lucas_262790815093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787208 : Nat.totient 288807105787208 = 143070811107840 := by
  rw [← show ((([(2, 3), (109, 1), (18041, 1), (18358229, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_109, prime_t32_18041, prime_t32_18358229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787209 : Nat.totient 288807105787209 = 190738649304312 := by
  rw [← show ((([(3, 2), (107, 1), (299903536643, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_107, prime_lucas_299903536643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787210 : Nat.totient 288807105787210 = 115521847172800 := by
  rw [← show ((([(2, 1), (5, 1), (116141, 1), (248669381, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_t32_116141, prime_lucas_248669381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787211 : Nat.totient 288807105787211 = 262262740014720 := by
  rw [← show ((([(11, 1), (1663, 1), (1999, 1), (7897873, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_11, prime_t32_1663, prime_t32_1999, prime_t32_7897873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787212 : Nat.totient 288807105787212 = 96269035262400 := by
  rw [← show ((([(2, 2), (3, 1), (24067258815601, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_lucas_24067258815601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787213 : Nat.totient 288807105787213 = 263992623111360 := by
  rw [← show ((([(13, 1), (103, 1), (25741, 1), (8379187, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_13, prime_t32_103, prime_t32_25741, prime_t32_8379187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787214 : Nat.totient 288807105787214 = 123774473908764 := by
  rw [← show ((([(2, 1), (7, 2), (2947011283543, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_7, prime_lucas_2947011283543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787215 : Nat.totient 288807105787215 = 154030272458112 := by
  rw [← show ((([(3, 1), (5, 1), (870229, 1), (22124989, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_5, prime_t32_870229, prime_t32_22124989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787216 : Nat.totient 288807105787216 = 144403552893600 := by
  rw [← show ((([(2, 4), (18050444111701, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_lucas_18050444111701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787217 : Nat.totient 288807105787217 = 271818452505600 := by
  rw [← show ((([(17, 1), (16988653281601, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_17, prime_lucas_16988653281601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787218 : Nat.totient 288807105787218 = 96237432225792 := by
  rw [← show ((([(2, 1), (3, 2), (3433, 1), (33529, 1), (139393, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_3433, prime_t32_33529, prime_t32_139393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787219 : Nat.totient 288807105787219 = 267242725413216 := by
  rw [← show ((([(19, 1), (43, 1), (330103, 1), (1070869, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_19, prime_t32_43, prime_t32_330103, prime_t32_1070869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787220 : Nat.totient 288807105787220 = 115522842314880 := by
  rw [← show ((([(2, 2), (5, 1), (14440355289361, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_lucas_14440355289361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787221 : Nat.totient 288807105787221 = 163955062656000 := by
  rw [← show ((([(3, 1), (7, 1), (251, 1), (433, 1), (4789, 1), (26423, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_7, prime_t32_251, prime_t32_433, prime_t32_4789, prime_t32_26423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787222 : Nat.totient 288807105787222 = 127558514578080 := by
  rw [← show ((([(2, 1), (11, 1), (47, 1), (139, 1), (2009428397, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_11, prime_t32_47, prime_t32_139, prime_lucas_2009428397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787223 : Nat.totient 288807105787223 = 269662798020000 := by
  rw [← show ((([(23, 1), (71, 1), (101, 1), (1751057131, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_23, prime_t32_71, prime_t32_101, prime_lucas_1751057131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787224 : Nat.totient 288807105787224 = 95511011361696 := by
  rw [← show ((([(2, 3), (3, 1), (127, 1), (94752987463, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_127, prime_lucas_94752987463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787225 : Nat.totient 288807105787225 = 230791213176000 := by
  rw [← show ((([(5, 2), (1061, 1), (6311, 1), (1725259, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_5, prime_t32_1061, prime_t32_6311, prime_t32_1725259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787226 : Nat.totient 288807105787226 = 133295587286400 := by
  rw [← show ((([(2, 1), (13, 1), (11107965607201, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_13, prime_lucas_11107965607201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787227 : Nat.totient 288807105787227 = 192277531850472 := by
  rw [← show ((([(3, 3), (739, 1), (14474370059, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_739, prime_lucas_14474370059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787228 : Nat.totient 288807105787228 = 120755098224000 := by
  rw [← show ((([(2, 2), (7, 1), (41, 1), (437071, 1), (575591, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_7, prime_t32_41, prime_t32_437071, prime_t32_575591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787229 : Nat.totient 288807105787229 = 278846075462976 := by
  rw [← show ((([(29, 1), (129037, 1), (77178373, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_29, prime_t32_129037, prime_lucas_77178373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787230 : Nat.totient 288807105787230 = 76854444848672 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (479, 1), (20097919679, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_5, prime_t32_479, prime_lucas_20097919679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787231 : Nat.totient 288807105787231 = 274737389477760 := by
  rw [← show ((([(31, 1), (59, 1), (16963, 1), (9308753, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_31, prime_t32_59, prime_t32_16963, prime_t32_9308753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787232 : Nat.totient 288807105787232 = 144403552893600 := by
  rw [← show ((([(2, 5), (9025222055851, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_lucas_9025222055851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787233 : Nat.totient 288807105787233 = 168673533235200 := by
  rw [← show ((([(3, 1), (11, 1), (37, 1), (163, 1), (421, 1), (1619, 1), (2129, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_11, prime_t32_37, prime_t32_163, prime_t32_421, prime_t32_1619, prime_t32_2129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787234 : Nat.totient 288807105787234 = 135301404157440 := by
  rw [← show ((([(2, 1), (17, 1), (263, 1), (1487, 1), (21720121, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_17, prime_t32_263, prime_t32_1487, prime_t32_21720121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787235 : Nat.totient 288807105787235 = 198039158254080 := by
  rw [← show ((([(5, 1), (7, 1), (8251631593921, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_5, prime_t32_7, prime_lucas_8251631593921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787236 : Nat.totient 288807105787236 = 96024391848000 := by
  rw [← show ((([(2, 2), (3, 2), (661, 1), (971, 1), (12499271, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_661, prime_t32_971, prime_t32_12499271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787237 : Nat.totient 288807105787237 = 287608070077440 := by
  rw [← show ((([(241, 1), (535013, 1), (2239889, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_241, prime_t32_535013, prime_t32_2239889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787238 : Nat.totient 288807105787238 = 136772421832800 := by
  rw [← show ((([(2, 1), (19, 1), (4421, 1), (1719110381, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_19, prime_t32_4421, prime_lucas_1719110381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787239 : Nat.totient 288807105787239 = 177727272345600 := by
  rw [← show ((([(3, 1), (13, 1), (1195361, 1), (6195041, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_13, prime_t32_1195361, prime_t32_6195041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787240 : Nat.totient 288807105787240 = 113798620786752 := by
  rw [← show ((([(2, 3), (5, 1), (67, 1), (107763845443, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_t32_67, prime_lucas_107763845443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787241 : Nat.totient 288807105787241 = 288380507402832 := by
  rw [← show ((([(677, 1), (426598383733, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_677, prime_lucas_426598383733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787242 : Nat.totient 288807105787242 = 82511734791744 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (18013, 1), (381744277, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_7, prime_t32_18013, prime_lucas_381744277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787243 : Nat.totient 288807105787243 = 283317510082464 := by
  rw [← show ((([(53, 1), (7013, 1), (777012787, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_53, prime_t32_7013, prime_lucas_777012787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787244 : Nat.totient 288807105787244 = 131275957176000 := by
  rw [← show ((([(2, 2), (11, 1), (6563797858801, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_11, prime_lucas_6563797858801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787245 : Nat.totient 288807105787245 = 154030456419840 := by
  rw [← show ((([(3, 2), (5, 1), (6417935684161, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_3, prime_t32_5, prime_lucas_6417935684161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787246 : Nat.totient 288807105787246 = 138125137550400 := by
  rw [← show ((([(2, 1), (23, 1), (6278415343201, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_23, prime_lucas_6278415343201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787247 : Nat.totient 288807105787247 = 288807105787246 := by
  rw [← show ((([(288807105787247, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_288807105787247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787248 : Nat.totient 288807105787248 = 96215670557952 := by
  rw [← show ((([(2, 4), (3, 1), (2293, 1), (8699, 1), (301643, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_3, prime_t32_2293, prime_t32_8699, prime_t32_301643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787249 : Nat.totient 288807105787249 = 243713746805760 := by
  rw [← show ((([(7, 1), (73, 1), (1021, 1), (1193, 1), (464003, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_7, prime_t32_73, prime_t32_1021, prime_t32_1193, prime_t32_464003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t32_288807105787250 : Nat.totient 288807105787250 = 115522842314800 := by
  rw [← show ((([(2, 1), (5, 3), (1155228423149, 1)] : List FactorBlock).map factorBlockValue).prod) = 288807105787250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t32_2, prime_t32_5, prime_lucas_1155228423149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The nineteenth finite diagonal certificate -/

theorem certifiedKill_diagonal_t32 :
    certifiedKill (periodLcm 32) (periodLcm 32) 50 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t32_144403552893601, phi_t32_144403552893602, phi_t32_144403552893603, phi_t32_144403552893604, phi_t32_144403552893605, phi_t32_144403552893606, phi_t32_144403552893607, phi_t32_144403552893608, phi_t32_144403552893609, phi_t32_144403552893610, phi_t32_144403552893611, phi_t32_144403552893612, phi_t32_144403552893613, phi_t32_144403552893614, phi_t32_144403552893615, phi_t32_144403552893616, phi_t32_144403552893617, phi_t32_144403552893618, phi_t32_144403552893619, phi_t32_144403552893620, phi_t32_144403552893621, phi_t32_144403552893622, phi_t32_144403552893623, phi_t32_144403552893624, phi_t32_144403552893625, phi_t32_144403552893626, phi_t32_144403552893627, phi_t32_144403552893628, phi_t32_144403552893629, phi_t32_144403552893630, phi_t32_144403552893631, phi_t32_144403552893632, phi_t32_144403552893633, phi_t32_144403552893634, phi_t32_144403552893635, phi_t32_144403552893636, phi_t32_144403552893637, phi_t32_144403552893638, phi_t32_144403552893639, phi_t32_144403552893640, phi_t32_144403552893641, phi_t32_144403552893642, phi_t32_144403552893643, phi_t32_144403552893644, phi_t32_144403552893645, phi_t32_144403552893646, phi_t32_144403552893647, phi_t32_144403552893648, phi_t32_144403552893649, phi_t32_144403552893650, phi_t32_288807105787201, phi_t32_288807105787202, phi_t32_288807105787203, phi_t32_288807105787204, phi_t32_288807105787205, phi_t32_288807105787206, phi_t32_288807105787207, phi_t32_288807105787208, phi_t32_288807105787209, phi_t32_288807105787210, phi_t32_288807105787211, phi_t32_288807105787212, phi_t32_288807105787213, phi_t32_288807105787214, phi_t32_288807105787215, phi_t32_288807105787216, phi_t32_288807105787217, phi_t32_288807105787218, phi_t32_288807105787219, phi_t32_288807105787220, phi_t32_288807105787221, phi_t32_288807105787222, phi_t32_288807105787223, phi_t32_288807105787224, phi_t32_288807105787225, phi_t32_288807105787226, phi_t32_288807105787227, phi_t32_288807105787228, phi_t32_288807105787229, phi_t32_288807105787230, phi_t32_288807105787231, phi_t32_288807105787232, phi_t32_288807105787233, phi_t32_288807105787234, phi_t32_288807105787235, phi_t32_288807105787236, phi_t32_288807105787237, phi_t32_288807105787238, phi_t32_288807105787239, phi_t32_288807105787240, phi_t32_288807105787241, phi_t32_288807105787242, phi_t32_288807105787243, phi_t32_288807105787244, phi_t32_288807105787245, phi_t32_288807105787246, phi_t32_288807105787247, phi_t32_288807105787248, phi_t32_288807105787249, phi_t32_288807105787250]

def diagonalPincerCertificateScalesThroughT32 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32]

def diagonalPincerKillDepthThroughT32 : ℕ → ℕ
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
  | _ => 0

/-- All 19 imported scales through t=32 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t32 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT32,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT32 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT32, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT32] using certifiedKill_diagonal_t32

#print axioms certifiedKill_diagonal_all_imported_through_t32

end TotientTailPeriodKiller
end Erdos249257
