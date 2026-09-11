import Erdos249257.DiagonalPincerCertificatesT29
import Erdos249257.DiagonalPincerPrimeCertificates.Prime65863351
import Erdos249257.DiagonalPincerPrimeCertificates.Prime104090537
import Erdos249257.DiagonalPincerPrimeCertificates.Prime231823871
import Erdos249257.DiagonalPincerPrimeCertificates.Prime246258553
import Erdos249257.DiagonalPincerPrimeCertificates.Prime248669381
import Erdos249257.DiagonalPincerPrimeCertificates.Prime381744277
import Erdos249257.DiagonalPincerPrimeCertificates.Prime579342971
import Erdos249257.DiagonalPincerPrimeCertificates.Prime797025869
import Erdos249257.DiagonalPincerPrimeCertificates.Prime823412819
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1577318983
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1719110381
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2009428397
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10714019357
import Erdos249257.DiagonalPincerPrimeCertificates.Prime17026712993
import Erdos249257.DiagonalPincerPrimeCertificates.Prime20097919679
import Erdos249257.DiagonalPincerPrimeCertificates.Prime48327828947
import Erdos249257.DiagonalPincerPrimeCertificates.Prime80179651801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime94752987463
import Erdos249257.DiagonalPincerPrimeCertificates.Prime107763845443
import Erdos249257.DiagonalPincerPrimeCertificates.Prime142409815477
import Erdos249257.DiagonalPincerPrimeCertificates.Prime594253304089
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1155228423149
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1719089915401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1827893074603
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1900046748601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2187932619601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2947011283543
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3702655202401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4813451763121
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5553982803601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime6278415343201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime6563797858801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime9025222055851
import Erdos249257.DiagonalPincerPrimeCertificates.Prime11107965607201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime14440355289361
import Erdos249257.DiagonalPincerPrimeCertificates.Prime18050444111701
import Erdos249257.DiagonalPincerPrimeCertificates.Prime20629078984807
import Erdos249257.DiagonalPincerPrimeCertificates.Prime24067258815601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime72201776446801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime144403552893641
import Erdos249257.DiagonalPincerPrimeCertificates.Prime144403552893643

/-!
# The t=31 diagonal-pincer certificate

This generated extension consumes 41 new large-prime Lucas roots
and 5 recursive Pratt dependencies, reuses 1 earlier certificates,
reconstructs all 98 Euler totients in the t=31 window, and proves the
eighteenth finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=31 window -/

private theorem prime_t31_2 : Nat.Prime 2 := by norm_num
private theorem prime_t31_3 : Nat.Prime 3 := by norm_num
private theorem prime_t31_5 : Nat.Prime 5 := by norm_num
private theorem prime_t31_7 : Nat.Prime 7 := by norm_num
private theorem prime_t31_11 : Nat.Prime 11 := by norm_num
private theorem prime_t31_13 : Nat.Prime 13 := by norm_num
private theorem prime_t31_17 : Nat.Prime 17 := by norm_num
private theorem prime_t31_19 : Nat.Prime 19 := by norm_num
private theorem prime_t31_23 : Nat.Prime 23 := by norm_num
private theorem prime_t31_29 : Nat.Prime 29 := by norm_num
private theorem prime_t31_31 : Nat.Prime 31 := by norm_num
private theorem prime_t31_37 : Nat.Prime 37 := by norm_num
private theorem prime_t31_41 : Nat.Prime 41 := by norm_num
private theorem prime_t31_43 : Nat.Prime 43 := by norm_num
private theorem prime_t31_47 : Nat.Prime 47 := by norm_num
private theorem prime_t31_53 : Nat.Prime 53 := by norm_num
private theorem prime_t31_59 : Nat.Prime 59 := by norm_num
private theorem prime_t31_61 : Nat.Prime 61 := by norm_num
private theorem prime_t31_67 : Nat.Prime 67 := by norm_num
private theorem prime_t31_71 : Nat.Prime 71 := by norm_num
private theorem prime_t31_79 : Nat.Prime 79 := by norm_num
private theorem prime_t31_83 : Nat.Prime 83 := by norm_num
private theorem prime_t31_89 : Nat.Prime 89 := by norm_num
private theorem prime_t31_97 : Nat.Prime 97 := by norm_num
private theorem prime_t31_101 : Nat.Prime 101 := by norm_num
private theorem prime_t31_103 : Nat.Prime 103 := by norm_num
private theorem prime_t31_107 : Nat.Prime 107 := by norm_num
private theorem prime_t31_109 : Nat.Prime 109 := by norm_num
private theorem prime_t31_113 : Nat.Prime 113 := by norm_num
private theorem prime_t31_127 : Nat.Prime 127 := by norm_num
private theorem prime_t31_139 : Nat.Prime 139 := by norm_num
private theorem prime_t31_157 : Nat.Prime 157 := by norm_num
private theorem prime_t31_163 : Nat.Prime 163 := by norm_num
private theorem prime_t31_191 : Nat.Prime 191 := by norm_num
private theorem prime_t31_197 : Nat.Prime 197 := by norm_num
private theorem prime_t31_211 : Nat.Prime 211 := by norm_num
private theorem prime_t31_257 : Nat.Prime 257 := by norm_num
private theorem prime_t31_263 : Nat.Prime 263 := by norm_num
private theorem prime_t31_271 : Nat.Prime 271 := by norm_num
private theorem prime_t31_277 : Nat.Prime 277 := by norm_num
private theorem prime_t31_283 : Nat.Prime 283 := by norm_num
private theorem prime_t31_293 : Nat.Prime 293 := by norm_num
private theorem prime_t31_313 : Nat.Prime 313 := by norm_num
private theorem prime_t31_353 : Nat.Prime 353 := by norm_num
private theorem prime_t31_359 : Nat.Prime 359 := by norm_num
private theorem prime_t31_379 : Nat.Prime 379 := by norm_num
private theorem prime_t31_397 : Nat.Prime 397 := by norm_num
private theorem prime_t31_479 : Nat.Prime 479 := by norm_num
private theorem prime_t31_487 : Nat.Prime 487 := by norm_num
private theorem prime_t31_523 : Nat.Prime 523 := by norm_num
private theorem prime_t31_563 : Nat.Prime 563 := by norm_num
private theorem prime_t31_577 : Nat.Prime 577 := by norm_num
private theorem prime_t31_661 : Nat.Prime 661 := by norm_num
private theorem prime_t31_773 : Nat.Prime 773 := by norm_num
private theorem prime_t31_823 : Nat.Prime 823 := by norm_num
private theorem prime_t31_827 : Nat.Prime 827 := by norm_num
private theorem prime_t31_971 : Nat.Prime 971 := by norm_num
private theorem prime_t31_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_t31_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_t31_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_t31_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_t31_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_t31_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_t31_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_t31_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_t31_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_t31_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_t31_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_t31_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_t31_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_t31_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_t31_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_t31_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_t31_6907 : Nat.Prime 6907 := by norm_num
private theorem prime_t31_7331 : Nat.Prime 7331 := by norm_num
private theorem prime_t31_8377 : Nat.Prime 8377 := by norm_num
private theorem prime_t31_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_t31_9697 : Nat.Prime 9697 := by norm_num
private theorem prime_t31_12107 : Nat.Prime 12107 := by norm_num
private theorem prime_t31_13367 : Nat.Prime 13367 := by norm_num
private theorem prime_t31_14627 : Nat.Prime 14627 := by norm_num
private theorem prime_t31_14831 : Nat.Prime 14831 := by norm_num
private theorem prime_t31_18013 : Nat.Prime 18013 := by norm_num
private theorem prime_t31_18041 : Nat.Prime 18041 := by norm_num
private theorem prime_t31_19037 : Nat.Prime 19037 := by norm_num
private theorem prime_t31_21559 : Nat.Prime 21559 := by norm_num
private theorem prime_t31_22051 : Nat.Prime 22051 := by norm_num
private theorem prime_t31_24247 : Nat.Prime 24247 := by norm_num
private theorem prime_t31_32579 : Nat.Prime 32579 := by norm_num
private theorem prime_t31_33529 : Nat.Prime 33529 := by norm_num
private theorem prime_t31_36821 : Nat.Prime 36821 := by norm_num
private theorem prime_t31_46337 : Nat.Prime 46337 := by norm_num
private theorem prime_t31_57143 : Nat.Prime 57143 := by norm_num
private theorem prime_t31_57737 : Nat.Prime 57737 := by norm_num
private theorem prime_t31_65027 : Nat.Prime 65027 := by norm_num
private theorem prime_t31_85909 : Nat.Prime 85909 := by norm_num
private theorem prime_t31_88843 : Nat.Prime 88843 := by norm_num
private theorem prime_t31_99391 : Nat.Prime 99391 := by norm_num
private theorem prime_t31_116141 : Nat.Prime 116141 := by norm_num
private theorem prime_t31_139393 : Nat.Prime 139393 := by norm_num
private theorem prime_t31_146317 : Nat.Prime 146317 := by norm_num
private theorem prime_t31_149497 : Nat.Prime 149497 := by norm_num
private theorem prime_t31_178813 : Nat.Prime 178813 := by norm_num
private theorem prime_t31_301643 : Nat.Prime 301643 := by norm_num
private theorem prime_t31_340939 : Nat.Prime 340939 := by norm_num
private theorem prime_t31_437071 : Nat.Prime 437071 := by norm_num
private theorem prime_t31_575591 : Nat.Prime 575591 := by norm_num
private theorem prime_t31_649073 : Nat.Prime 649073 := by norm_num
private theorem prime_t31_691343 : Nat.Prime 691343 := by norm_num
private theorem prime_t31_855581 : Nat.Prime 855581 := by norm_num
private theorem prime_t31_974999 : Nat.Prime 974999 := by norm_num
private theorem prime_t31_1061729 : Nat.Prime 1061729 := by norm_num
private theorem prime_t31_1314011 : Nat.Prime 1314011 := by norm_num
private theorem prime_t31_1700099 : Nat.Prime 1700099 := by norm_num
private theorem prime_t31_1883503 : Nat.Prime 1883503 := by norm_num
private theorem prime_t31_2017567 : Nat.Prime 2017567 := by norm_num
private theorem prime_t31_2047567 : Nat.Prime 2047567 := by norm_num
private theorem prime_t31_2807473 : Nat.Prime 2807473 := by norm_num
private theorem prime_t31_3718417 : Nat.Prime 3718417 := by norm_num
private theorem prime_t31_3814439 : Nat.Prime 3814439 := by norm_num
private theorem prime_t31_4119937 : Nat.Prime 4119937 := by norm_num
private theorem prime_t31_4464763 : Nat.Prime 4464763 := by norm_num
private theorem prime_t31_4806523 : Nat.Prime 4806523 := by norm_num
private theorem prime_t31_5630201 : Nat.Prime 5630201 := by norm_num
private theorem prime_t31_6550651 : Nat.Prime 6550651 := by norm_num
private theorem prime_t31_12237359 : Nat.Prime 12237359 := by norm_num
private theorem prime_t31_12499271 : Nat.Prime 12499271 := by norm_num
private theorem prime_t31_16143151 : Nat.Prime 16143151 := by norm_num
private theorem prime_t31_16144279 : Nat.Prime 16144279 := by norm_num
private theorem prime_t31_18358229 : Nat.Prime 18358229 := by norm_num
private theorem prime_t31_21720121 : Nat.Prime 21720121 := by norm_num

/-! ## Exact t=31 window totients -/

private theorem phi_t31_72201776446801 : Nat.totient 72201776446801 = 72201776446800 := by
  rw [← show ((([(72201776446801, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_72201776446801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446802 : Nat.totient 72201776446802 = 35767702776960 := by
  rw [← show ((([(2, 1), (109, 1), (18041, 1), (18358229, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_109, prime_t31_18041, prime_t31_18358229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446803 : Nat.totient 72201776446803 = 48134517631200 := by
  rw [← show ((([(3, 1), (24067258815601, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_lucas_24067258815601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446804 : Nat.totient 72201776446804 = 36100888223400 := by
  rw [← show ((([(2, 2), (18050444111701, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_lucas_18050444111701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446805 : Nat.totient 72201776446805 = 57761421157440 := by
  rw [← show ((([(5, 1), (14440355289361, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_5, prime_lucas_14440355289361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446806 : Nat.totient 72201776446806 = 23877752840424 := by
  rw [← show ((([(2, 1), (3, 1), (127, 1), (94752987463, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_127, prime_lucas_94752987463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446807 : Nat.totient 72201776446807 = 60377549112000 := by
  rw [← show ((([(7, 1), (41, 1), (437071, 1), (575591, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_7, prime_t31_41, prime_t31_437071, prime_t31_575591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446808 : Nat.totient 72201776446808 = 36100888223400 := by
  rw [← show ((([(2, 3), (9025222055851, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_lucas_9025222055851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446809 : Nat.totient 72201776446809 = 48012195924000 := by
  rw [← show ((([(3, 2), (661, 1), (971, 1), (12499271, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_661, prime_t31_971, prime_t31_12499271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446810 : Nat.totient 72201776446810 = 28449655196688 := by
  rw [← show ((([(2, 1), (5, 1), (67, 1), (107763845443, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_5, prime_t31_67, prime_lucas_107763845443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446811 : Nat.totient 72201776446811 = 65637978588000 := by
  rw [← show ((([(11, 1), (6563797858801, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_11, prime_lucas_6563797858801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446812 : Nat.totient 72201776446812 = 24053917639488 := by
  rw [← show ((([(2, 2), (3, 1), (2293, 1), (8699, 1), (301643, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_2293, prime_t31_8699, prime_t31_301643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446813 : Nat.totient 72201776446813 = 66647793643200 := by
  rw [← show ((([(13, 1), (5553982803601, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_13, prime_lucas_5553982803601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446814 : Nat.totient 72201776446814 = 30869665934400 := by
  rw [← show ((([(2, 1), (7, 1), (563, 1), (1627, 1), (5630201, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_7, prime_t31_563, prime_t31_1627, prime_t31_5630201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446815 : Nat.totient 72201776446815 = 38507614104960 := by
  rw [← show ((([(3, 1), (5, 1), (4813451763121, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_5, prime_lucas_4813451763121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446816 : Nat.totient 72201776446816 = 35505399214080 := by
  rw [← show ((([(2, 5), (61, 1), (9697, 1), (3814439, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_61, prime_t31_9697, prime_t31_3814439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446817 : Nat.totient 72201776446817 = 67945343521600 := by
  rw [← show ((([(17, 1), (7331, 1), (579342971, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_17, prime_t31_7331, prime_lucas_579342971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446818 : Nat.totient 72201776446818 = 23777291841432 := by
  rw [← show ((([(2, 1), (3, 2), (83, 1), (48327828947, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_83, prime_lucas_48327828947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446819 : Nat.totient 72201776446819 = 68401612730376 := by
  rw [← show ((([(19, 1), (1883503, 1), (2017567, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_19, prime_t31_1883503, prime_t31_2017567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446820 : Nat.totient 72201776446820 = 28774265775744 := by
  rw [← show ((([(2, 2), (5, 1), (277, 1), (13367, 1), (974999, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_5, prime_t31_277, prime_t31_13367, prime_t31_974999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446821 : Nat.totient 72201776446821 = 41255375905200 := by
  rw [← show ((([(3, 1), (7, 1), (14831, 1), (231823871, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_7, prime_t31_14831, prime_lucas_231823871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446822 : Nat.totient 72201776446822 = 32734875682080 := by
  rw [← show ((([(2, 1), (11, 1), (397, 1), (24247, 1), (340939, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_11, prime_t31_397, prime_t31_24247, prime_t31_340939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446823 : Nat.totient 72201776446823 = 68826860342944 := by
  rw [← show ((([(23, 1), (293, 1), (10714019357, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_23, prime_t31_293, prime_lucas_10714019357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446824 : Nat.totient 72201776446824 = 23267410403328 := by
  rw [← show ((([(2, 3), (3, 1), (53, 1), (97, 1), (379, 1), (827, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_53, prime_t31_97, prime_t31_379, prime_t31_827, prime_t31_1867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446825 : Nat.totient 72201776446825 = 57729874741200 := by
  rw [← show ((([(5, 2), (1831, 1), (1577318983, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_5, prime_t31_1831, prime_lucas_1577318983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446826 : Nat.totient 72201776446826 = 33164173506240 := by
  rw [← show ((([(2, 1), (13, 1), (211, 1), (19037, 1), (691343, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_13, prime_t31_211, prime_t31_19037, prime_t31_691343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446827 : Nat.totient 72201776446827 = 48134431789056 := by
  rw [← show ((([(3, 3), (649073, 1), (4119937, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_649073, prime_t31_4119937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446828 : Nat.totient 72201776446828 = 30934874574912 := by
  rw [← show ((([(2, 2), (7, 2), (3539, 1), (104090537, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_7, prime_t31_3539, prime_lucas_104090537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446829 : Nat.totient 72201776446829 = 66934933232832 := by
  rw [← show ((([(29, 1), (47, 1), (103, 1), (107, 1), (4806523, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_29, prime_t31_47, prime_t31_103, prime_t31_107, prime_t31_4806523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446830 : Nat.totient 72201776446830 = 19211553355776 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (773, 1), (1109, 1), (2807473, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_5, prime_t31_773, prime_t31_1109, prime_t31_2807473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446831 : Nat.totient 72201776446831 = 68893902000000 := by
  rw [← show ((([(31, 1), (101, 1), (271, 1), (2311, 1), (36821, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_31, prime_t31_101, prime_t31_271, prime_t31_2311, prime_t31_36821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446832 : Nat.totient 72201776446832 = 35999663553792 := by
  rw [← show ((([(2, 4), (359, 1), (85909, 1), (146317, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_359, prime_t31_85909, prime_t31_146317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446833 : Nat.totient 72201776446833 = 43758652392000 := by
  rw [← show ((([(3, 1), (11, 1), (2187932619601, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_11, prime_lucas_2187932619601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446834 : Nat.totient 72201776446834 = 33964131916864 := by
  rw [← show ((([(2, 1), (17, 1), (2579, 1), (823412819, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_17, prime_t31_2579, prime_lucas_823412819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446835 : Nat.totient 72201776446835 = 49503879157248 := by
  rw [← show ((([(5, 1), (7, 1), (8377, 1), (246258553, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_5, prime_t31_7, prime_t31_8377, prime_lucas_246258553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446836 : Nat.totient 72201776446836 = 23388339038400 := by
  rw [← show ((([(2, 2), (3, 2), (37, 1), (823, 1), (65863351, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_37, prime_t31_823, prime_lucas_65863351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446837 : Nat.totient 72201776446837 = 69727032144000 := by
  rw [← show ((([(43, 1), (89, 1), (22051, 1), (855581, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_43, prime_t31_89, prime_t31_22051, prime_t31_855581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446838 : Nat.totient 72201776446838 = 34200841474800 := by
  rw [← show ((([(2, 1), (19, 1), (1900046748601, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_19, prime_lucas_1900046748601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446839 : Nat.totient 72201776446839 = 44431862428512 := by
  rw [← show ((([(3, 1), (13, 2), (142409815477, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_13, prime_lucas_142409815477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446840 : Nat.totient 72201776446840 = 28880666389504 := by
  rw [← show ((([(2, 3), (5, 1), (1061729, 1), (1700099, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_5, prime_t31_1061729, prime_t31_1700099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446841 : Nat.totient 72201776446841 = 71617556395008 := by
  rw [← show ((([(157, 1), (577, 1), (797025869, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_157, prime_t31_577, prime_lucas_797025869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446842 : Nat.totient 72201776446842 = 20629078984800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1719089915401, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_7, prime_lucas_1719089915401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446843 : Nat.totient 72201776446843 = 71483313749760 := by
  rw [← show ((([(191, 1), (353, 1), (523, 1), (2047567, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_191, prime_t31_353, prime_t31_523, prime_t31_2047567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446844 : Nat.totient 72201776446844 = 32787082997760 := by
  rw [← show ((([(2, 2), (11, 1), (1087, 1), (32579, 1), (46337, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_11, prime_t31_1087, prime_t31_32579, prime_t31_46337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446845 : Nat.totient 72201776446845 = 38507224284000 := by
  rw [← show ((([(3, 2), (5, 1), (99391, 1), (16143151, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_5, prime_t31_99391, prime_t31_16143151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446846 : Nat.totient 72201776446846 = 34458549339456 := by
  rw [← show ((([(2, 1), (23, 1), (487, 1), (21559, 1), (149497, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_23, prime_t31_487, prime_t31_21559, prime_t31_149497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446847 : Nat.totient 72201776446847 = 71945371317528 := by
  rw [← show ((([(283, 1), (57143, 1), (4464763, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_283, prime_t31_57143, prime_t31_4464763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446848 : Nat.totient 72201776446848 = 23461338501120 := by
  rw [← show ((([(2, 7), (3, 1), (41, 2), (1259, 1), (88843, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_41, prime_t31_1259, prime_t31_88843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_72201776446849 : Nat.totient 72201776446849 = 61495660915920 := by
  rw [← show ((([(7, 1), (163, 1), (5171, 1), (12237359, 1)] : List FactorBlock).map factorBlockValue).prod) = 72201776446849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_7, prime_t31_163, prime_t31_5171, prime_t31_12237359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893601 : Nat.totient 144403552893601 = 144323373240000 := by
  rw [← show ((([(1801, 1), (80179651801, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_1801, prime_lucas_80179651801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893602 : Nat.totient 144403552893602 = 72201776446800 := by
  rw [← show ((([(2, 1), (72201776446801, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_lucas_72201776446801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893603 : Nat.totient 144403552893603 = 95415614985600 := by
  rw [← show ((([(3, 1), (113, 1), (65027, 1), (6550651, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_113, prime_t31_65027, prime_t31_6550651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893604 : Nat.totient 144403552893604 = 71535405553920 := by
  rw [← show ((([(2, 2), (109, 1), (18041, 1), (18358229, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_109, prime_t31_18041, prime_t31_18358229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893605 : Nat.totient 144403552893605 = 115521847172800 := by
  rw [← show ((([(5, 1), (116141, 1), (248669381, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_5, prime_t31_116141, prime_lucas_248669381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893606 : Nat.totient 144403552893606 = 48134517631200 := by
  rw [← show ((([(2, 1), (3, 1), (24067258815601, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_lucas_24067258815601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893607 : Nat.totient 144403552893607 = 123774473908764 := by
  rw [← show ((([(7, 2), (2947011283543, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_7, prime_lucas_2947011283543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893608 : Nat.totient 144403552893608 = 72201776446800 := by
  rw [← show ((([(2, 3), (18050444111701, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_lucas_18050444111701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893609 : Nat.totient 144403552893609 = 96237432225792 := by
  rw [← show ((([(3, 2), (3433, 1), (33529, 1), (139393, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_3433, prime_t31_33529, prime_t31_139393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893610 : Nat.totient 144403552893610 = 57761421157440 := by
  rw [← show ((([(2, 1), (5, 1), (14440355289361, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_5, prime_lucas_14440355289361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893611 : Nat.totient 144403552893611 = 127558514578080 := by
  rw [← show ((([(11, 1), (47, 1), (139, 1), (2009428397, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_11, prime_t31_47, prime_t31_139, prime_lucas_2009428397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893612 : Nat.totient 144403552893612 = 47755505680848 := by
  rw [← show ((([(2, 2), (3, 1), (127, 1), (94752987463, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_127, prime_lucas_94752987463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893613 : Nat.totient 144403552893613 = 133295587286400 := by
  rw [← show ((([(13, 1), (11107965607201, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_13, prime_lucas_11107965607201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893614 : Nat.totient 144403552893614 = 60377549112000 := by
  rw [← show ((([(2, 1), (7, 1), (41, 1), (437071, 1), (575591, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_7, prime_t31_41, prime_t31_437071, prime_t31_575591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893615 : Nat.totient 144403552893615 = 76854444848672 := by
  rw [← show ((([(3, 1), (5, 1), (479, 1), (20097919679, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_5, prime_t31_479, prime_lucas_20097919679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893616 : Nat.totient 144403552893616 = 72201776446800 := by
  rw [← show ((([(2, 4), (9025222055851, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_lucas_9025222055851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893617 : Nat.totient 144403552893617 = 135301404157440 := by
  rw [← show ((([(17, 1), (263, 1), (1487, 1), (21720121, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_17, prime_t31_263, prime_t31_1487, prime_t31_21720121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893618 : Nat.totient 144403552893618 = 48012195924000 := by
  rw [← show ((([(2, 1), (3, 2), (661, 1), (971, 1), (12499271, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_661, prime_t31_971, prime_t31_12499271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893619 : Nat.totient 144403552893619 = 136772421832800 := by
  rw [← show ((([(19, 1), (4421, 1), (1719110381, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_19, prime_t31_4421, prime_lucas_1719110381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893620 : Nat.totient 144403552893620 = 56899310393376 := by
  rw [← show ((([(2, 2), (5, 1), (67, 1), (107763845443, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_5, prime_t31_67, prime_lucas_107763845443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893621 : Nat.totient 144403552893621 = 82511734791744 := by
  rw [← show ((([(3, 1), (7, 1), (18013, 1), (381744277, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_7, prime_t31_18013, prime_lucas_381744277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893622 : Nat.totient 144403552893622 = 65637978588000 := by
  rw [← show ((([(2, 1), (11, 1), (6563797858801, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_11, prime_lucas_6563797858801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893623 : Nat.totient 144403552893623 = 138125137550400 := by
  rw [← show ((([(23, 1), (6278415343201, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_23, prime_lucas_6278415343201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893624 : Nat.totient 144403552893624 = 48107835278976 := by
  rw [← show ((([(2, 3), (3, 1), (2293, 1), (8699, 1), (301643, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_2293, prime_t31_8699, prime_t31_301643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893625 : Nat.totient 144403552893625 = 115522842314800 := by
  rw [← show ((([(5, 3), (1155228423149, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_5, prime_lucas_1155228423149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893626 : Nat.totient 144403552893626 = 66647793643200 := by
  rw [← show ((([(2, 1), (13, 1), (5553982803601, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_13, prime_lucas_5553982803601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893627 : Nat.totient 144403552893627 = 96269035262256 := by
  rw [← show ((([(3, 5), (594253304089, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_lucas_594253304089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893628 : Nat.totient 144403552893628 = 61739331868800 := by
  rw [← show ((([(2, 2), (7, 1), (563, 1), (1627, 1), (5630201, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_7, prime_t31_563, prime_t31_1627, prime_t31_5630201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893629 : Nat.totient 144403552893629 = 138967090604160 := by
  rw [← show ((([(29, 1), (313, 1), (12107, 1), (1314011, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_29, prime_t31_313, prime_t31_12107, prime_t31_1314011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893630 : Nat.totient 144403552893630 = 38507614104960 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (4813451763121, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_5, prime_lucas_4813451763121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893631 : Nat.totient 144403552893631 = 136437419916000 := by
  rw [← show ((([(31, 1), (43, 1), (2351, 1), (46078157, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_31, prime_t31_43, prime_t31_2351, prime_lucas_46078157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893632 : Nat.totient 144403552893632 = 71010798428160 := by
  rw [← show ((([(2, 6), (61, 1), (9697, 1), (3814439, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_61, prime_t31_9697, prime_t31_3814439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893633 : Nat.totient 144403552893633 = 87176770519040 := by
  rw [← show ((([(3, 1), (11, 1), (257, 1), (17026712993, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_11, prime_t31_257, prime_lucas_17026712993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893634 : Nat.totient 144403552893634 = 67945343521600 := by
  rw [← show ((([(2, 1), (17, 1), (7331, 1), (579342971, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_17, prime_t31_7331, prime_lucas_579342971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893635 : Nat.totient 144403552893635 = 96329419661952 := by
  rw [← show ((([(5, 1), (7, 1), (37, 1), (6907, 1), (16144279, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_5, prime_t31_7, prime_t31_37, prime_t31_6907, prime_t31_16144279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893636 : Nat.totient 144403552893636 = 47554583682864 := by
  rw [← show ((([(2, 2), (3, 2), (83, 1), (48327828947, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_83, prime_lucas_48327828947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893637 : Nat.totient 144403552893637 = 142575659818956 := by
  rw [← show ((([(79, 1), (1827893074603, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_79, prime_lucas_1827893074603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893638 : Nat.totient 144403552893638 = 68401612730376 := by
  rw [← show ((([(2, 1), (19, 1), (1883503, 1), (2017567, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_19, prime_t31_1883503, prime_t31_2017567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893639 : Nat.totient 144403552893639 = 88863724857600 := by
  rw [← show ((([(3, 1), (13, 1), (3702655202401, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_13, prime_lucas_3702655202401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893640 : Nat.totient 144403552893640 = 57548531551488 := by
  rw [← show ((([(2, 3), (5, 1), (277, 1), (13367, 1), (974999, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_5, prime_t31_277, prime_t31_13367, prime_t31_974999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893641 : Nat.totient 144403552893641 = 144403552893640 := by
  rw [← show ((([(144403552893641, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_144403552893641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893642 : Nat.totient 144403552893642 = 41255375905200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (14831, 1), (231823871, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_7, prime_t31_14831, prime_lucas_231823871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893643 : Nat.totient 144403552893643 = 144403552893642 := by
  rw [← show ((([(144403552893643, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_144403552893643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893644 : Nat.totient 144403552893644 = 65469751364160 := by
  rw [← show ((([(2, 2), (11, 1), (397, 1), (24247, 1), (340939, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_11, prime_t31_397, prime_t31_24247, prime_t31_340939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893645 : Nat.totient 144403552893645 = 75704688963072 := by
  rw [← show ((([(3, 2), (5, 1), (59, 1), (14627, 1), (3718417, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_3, prime_t31_5, prime_t31_59, prime_t31_14627, prime_t31_3718417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893646 : Nat.totient 144403552893646 = 68826860342944 := by
  rw [← show ((([(2, 1), (23, 1), (293, 1), (10714019357, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_23, prime_t31_293, prime_lucas_10714019357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893647 : Nat.totient 144403552893647 = 141643765751040 := by
  rw [← show ((([(71, 1), (197, 1), (57737, 1), (178813, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_71, prime_t31_197, prime_t31_57737, prime_t31_178813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893648 : Nat.totient 144403552893648 = 46534820806656 := by
  rw [← show ((([(2, 4), (3, 1), (53, 1), (97, 1), (379, 1), (827, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_2, prime_t31_3, prime_t31_53, prime_t31_97, prime_t31_379, prime_t31_827, prime_t31_1867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t31_144403552893649 : Nat.totient 144403552893649 = 123774473908836 := by
  rw [← show ((([(7, 1), (20629078984807, 1)] : List FactorBlock).map factorBlockValue).prod) = 144403552893649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t31_7, prime_lucas_20629078984807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The eighteenth finite diagonal certificate -/

theorem certifiedKill_diagonal_t31 :
    certifiedKill (periodLcm 31) (periodLcm 31) 49 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t31_72201776446801, phi_t31_72201776446802, phi_t31_72201776446803, phi_t31_72201776446804, phi_t31_72201776446805, phi_t31_72201776446806, phi_t31_72201776446807, phi_t31_72201776446808, phi_t31_72201776446809, phi_t31_72201776446810, phi_t31_72201776446811, phi_t31_72201776446812, phi_t31_72201776446813, phi_t31_72201776446814, phi_t31_72201776446815, phi_t31_72201776446816, phi_t31_72201776446817, phi_t31_72201776446818, phi_t31_72201776446819, phi_t31_72201776446820, phi_t31_72201776446821, phi_t31_72201776446822, phi_t31_72201776446823, phi_t31_72201776446824, phi_t31_72201776446825, phi_t31_72201776446826, phi_t31_72201776446827, phi_t31_72201776446828, phi_t31_72201776446829, phi_t31_72201776446830, phi_t31_72201776446831, phi_t31_72201776446832, phi_t31_72201776446833, phi_t31_72201776446834, phi_t31_72201776446835, phi_t31_72201776446836, phi_t31_72201776446837, phi_t31_72201776446838, phi_t31_72201776446839, phi_t31_72201776446840, phi_t31_72201776446841, phi_t31_72201776446842, phi_t31_72201776446843, phi_t31_72201776446844, phi_t31_72201776446845, phi_t31_72201776446846, phi_t31_72201776446847, phi_t31_72201776446848, phi_t31_72201776446849, phi_t31_144403552893601, phi_t31_144403552893602, phi_t31_144403552893603, phi_t31_144403552893604, phi_t31_144403552893605, phi_t31_144403552893606, phi_t31_144403552893607, phi_t31_144403552893608, phi_t31_144403552893609, phi_t31_144403552893610, phi_t31_144403552893611, phi_t31_144403552893612, phi_t31_144403552893613, phi_t31_144403552893614, phi_t31_144403552893615, phi_t31_144403552893616, phi_t31_144403552893617, phi_t31_144403552893618, phi_t31_144403552893619, phi_t31_144403552893620, phi_t31_144403552893621, phi_t31_144403552893622, phi_t31_144403552893623, phi_t31_144403552893624, phi_t31_144403552893625, phi_t31_144403552893626, phi_t31_144403552893627, phi_t31_144403552893628, phi_t31_144403552893629, phi_t31_144403552893630, phi_t31_144403552893631, phi_t31_144403552893632, phi_t31_144403552893633, phi_t31_144403552893634, phi_t31_144403552893635, phi_t31_144403552893636, phi_t31_144403552893637, phi_t31_144403552893638, phi_t31_144403552893639, phi_t31_144403552893640, phi_t31_144403552893641, phi_t31_144403552893642, phi_t31_144403552893643, phi_t31_144403552893644, phi_t31_144403552893645, phi_t31_144403552893646, phi_t31_144403552893647, phi_t31_144403552893648, phi_t31_144403552893649]

def diagonalPincerCertificateScalesThroughT31 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31]

def diagonalPincerKillDepthThroughT31 : ℕ → ℕ
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
  | _ => 0

/-- All 18 imported scales through t=31 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t31 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT31,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT31 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT31, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT31] using certifiedKill_diagonal_t31

#print axioms certifiedKill_diagonal_all_imported_through_t31

end TotientTailPeriodKiller
end Erdos249257
