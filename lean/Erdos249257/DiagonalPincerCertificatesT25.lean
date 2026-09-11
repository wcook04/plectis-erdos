import Erdos249257.DiagonalPincerCertificatesT23
import Erdos249257.DiagonalPincerPrimeCertificates.Prime34388111
import Erdos249257.DiagonalPincerPrimeCertificates.Prime35982721
import Erdos249257.DiagonalPincerPrimeCertificates.Prime40965791
import Erdos249257.DiagonalPincerPrimeCertificates.Prime58644347
import Erdos249257.DiagonalPincerPrimeCertificates.Prime205142869
import Erdos249257.DiagonalPincerPrimeCertificates.Prime491213659
import Erdos249257.DiagonalPincerPrimeCertificates.Prime836598263
import Erdos249257.DiagonalPincerPrimeCertificates.Prime991523867
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1029659401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1163962801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1245169507
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1574773201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1622493601
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2059318801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2549632801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3824449201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4461857401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime8923714801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime13385572201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime26771144401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime26771144429
import Erdos249257.DiagonalPincerPrimeCertificates.Prime53542288829

/-!
# The t=25 diagonal-pincer certificate

This generated extension consumes twenty-two new large-prime Lucas roots
and two recursive Pratt dependencies, reuses four earlier certificates,
reconstructs all 76 Euler totients in the t=25 window, and proves the
fifteenth finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=25 window -/

private theorem prime_t25_2 : Nat.Prime 2 := by norm_num
private theorem prime_t25_3 : Nat.Prime 3 := by norm_num
private theorem prime_t25_5 : Nat.Prime 5 := by norm_num
private theorem prime_t25_7 : Nat.Prime 7 := by norm_num
private theorem prime_t25_11 : Nat.Prime 11 := by norm_num
private theorem prime_t25_13 : Nat.Prime 13 := by norm_num
private theorem prime_t25_17 : Nat.Prime 17 := by norm_num
private theorem prime_t25_19 : Nat.Prime 19 := by norm_num
private theorem prime_t25_23 : Nat.Prime 23 := by norm_num
private theorem prime_t25_29 : Nat.Prime 29 := by norm_num
private theorem prime_t25_31 : Nat.Prime 31 := by norm_num
private theorem prime_t25_37 : Nat.Prime 37 := by norm_num
private theorem prime_t25_41 : Nat.Prime 41 := by norm_num
private theorem prime_t25_43 : Nat.Prime 43 := by norm_num
private theorem prime_t25_61 : Nat.Prime 61 := by norm_num
private theorem prime_t25_67 : Nat.Prime 67 := by norm_num
private theorem prime_t25_71 : Nat.Prime 71 := by norm_num
private theorem prime_t25_73 : Nat.Prime 73 := by norm_num
private theorem prime_t25_79 : Nat.Prime 79 := by norm_num
private theorem prime_t25_83 : Nat.Prime 83 := by norm_num
private theorem prime_t25_97 : Nat.Prime 97 := by norm_num
private theorem prime_t25_101 : Nat.Prime 101 := by norm_num
private theorem prime_t25_109 : Nat.Prime 109 := by norm_num
private theorem prime_t25_131 : Nat.Prime 131 := by norm_num
private theorem prime_t25_167 : Nat.Prime 167 := by norm_num
private theorem prime_t25_173 : Nat.Prime 173 := by norm_num
private theorem prime_t25_179 : Nat.Prime 179 := by norm_num
private theorem prime_t25_199 : Nat.Prime 199 := by norm_num
private theorem prime_t25_223 : Nat.Prime 223 := by norm_num
private theorem prime_t25_233 : Nat.Prime 233 := by norm_num
private theorem prime_t25_239 : Nat.Prime 239 := by norm_num
private theorem prime_t25_269 : Nat.Prime 269 := by norm_num
private theorem prime_t25_353 : Nat.Prime 353 := by norm_num
private theorem prime_t25_379 : Nat.Prime 379 := by norm_num
private theorem prime_t25_499 : Nat.Prime 499 := by norm_num
private theorem prime_t25_613 : Nat.Prime 613 := by norm_num
private theorem prime_t25_617 : Nat.Prime 617 := by norm_num
private theorem prime_t25_701 : Nat.Prime 701 := by norm_num
private theorem prime_t25_761 : Nat.Prime 761 := by norm_num
private theorem prime_t25_853 : Nat.Prime 853 := by norm_num
private theorem prime_t25_907 : Nat.Prime 907 := by norm_num
private theorem prime_t25_929 : Nat.Prime 929 := by norm_num
private theorem prime_t25_997 : Nat.Prime 997 := by norm_num
private theorem prime_t25_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_t25_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_t25_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_t25_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_t25_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_t25_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_t25_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_t25_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_t25_5417 : Nat.Prime 5417 := by norm_num
private theorem prime_t25_5791 : Nat.Prime 5791 := by norm_num
private theorem prime_t25_5981 : Nat.Prime 5981 := by norm_num
private theorem prime_t25_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_t25_6869 : Nat.Prime 6869 := by norm_num
private theorem prime_t25_11299 : Nat.Prime 11299 := by norm_num
private theorem prime_t25_11903 : Nat.Prime 11903 := by norm_num
private theorem prime_t25_19213 : Nat.Prime 19213 := by norm_num
private theorem prime_t25_19937 : Nat.Prime 19937 := by norm_num
private theorem prime_t25_21149 : Nat.Prime 21149 := by norm_num
private theorem prime_t25_23003 : Nat.Prime 23003 := by norm_num
private theorem prime_t25_28183 : Nat.Prime 28183 := by norm_num
private theorem prime_t25_35267 : Nat.Prime 35267 := by norm_num
private theorem prime_t25_35797 : Nat.Prime 35797 := by norm_num
private theorem prime_t25_37537 : Nat.Prime 37537 := by norm_num
private theorem prime_t25_49331 : Nat.Prime 49331 := by norm_num
private theorem prime_t25_59369 : Nat.Prime 59369 := by norm_num
private theorem prime_t25_62969 : Nat.Prime 62969 := by norm_num
private theorem prime_t25_84389 : Nat.Prime 84389 := by norm_num
private theorem prime_t25_103001 : Nat.Prime 103001 := by norm_num
private theorem prime_t25_119107 : Nat.Prime 119107 := by norm_num
private theorem prime_t25_135671 : Nat.Prime 135671 := by norm_num
private theorem prime_t25_189547 : Nat.Prime 189547 := by norm_num
private theorem prime_t25_571453 : Nat.Prime 571453 := by norm_num
private theorem prime_t25_804059 : Nat.Prime 804059 := by norm_num
private theorem prime_t25_1393387 : Nat.Prime 1393387 := by norm_num
private theorem prime_t25_1526117 : Nat.Prime 1526117 := by norm_num
private theorem prime_t25_2066153 : Nat.Prime 2066153 := by norm_num
private theorem prime_t25_4728631 : Nat.Prime 4728631 := by norm_num
private theorem prime_t25_4801999 : Nat.Prime 4801999 := by norm_num
private theorem prime_t25_4942061 : Nat.Prime 4942061 := by norm_num
private theorem prime_t25_8905903 : Nat.Prime 8905903 := by norm_num
private theorem prime_t25_9650737 : Nat.Prime 9650737 := by norm_num
private theorem prime_t25_18578171 : Nat.Prime 18578171 := by norm_num
private theorem prime_t25_25840873 : Nat.Prime 25840873 := by norm_num
private theorem prime_t25_32003759 : Nat.Prime 32003759 := by norm_num

/-! ## Exact t=25 window totients -/

private theorem phi_t25_26771144401 : Nat.totient 26771144401 = 26771144400 := by
  rw [← show ((([(26771144401, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_26771144401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144402 : Nat.totient 26771144402 = 13385572200 := by
  rw [← show ((([(2, 1), (13385572201, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_lucas_13385572201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144403 : Nat.totient 26771144403 = 17847429600 := by
  rw [← show ((([(3, 1), (8923714801, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_lucas_8923714801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144404 : Nat.totient 26771144404 = 13385202200 := by
  rw [← show ((([(2, 2), (49331, 1), (135671, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_49331, prime_t25_135671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144405 : Nat.totient 26771144405 = 21413672656 := by
  rw [← show ((([(5, 1), (6659, 1), (804059, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_5, prime_t25_6659, prime_t25_804059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144406 : Nat.totient 26771144406 = 8923714800 := by
  rw [← show ((([(2, 1), (3, 1), (4461857401, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_lucas_4461857401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144407 : Nat.totient 26771144407 = 22946695200 := by
  rw [← show ((([(7, 1), (3824449201, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_7, prime_lucas_3824449201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144408 : Nat.totient 26771144408 = 13337195520 := by
  rw [← show ((([(2, 3), (353, 1), (1637, 1), (5791, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_353, prime_t25_1637, prime_t25_5791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144409 : Nat.totient 26771144409 = 17847429588 := by
  rw [← show ((([(3, 3), (991523867, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_lucas_991523867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144410 : Nat.totient 26771144410 = 10708457760 := by
  rw [← show ((([(2, 1), (5, 1), (2677114441, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_5, prime_lucas_2677114441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144411 : Nat.totient 26771144411 = 24151621000 := by
  rw [← show ((([(11, 1), (131, 1), (18578171, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_11, prime_t25_131, prime_t25_18578171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144412 : Nat.totient 26771144412 = 8780257920 := by
  rw [← show ((([(2, 2), (3, 1), (71, 1), (499, 1), (62969, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_71, prime_t25_499, prime_t25_62969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144413 : Nat.totient 26771144413 = 24711825600 := by
  rw [← show ((([(13, 1), (2059318801, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_13, prime_lucas_2059318801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144414 : Nat.totient 26771144414 = 11409243216 := by
  rw [← show ((([(2, 1), (7, 2), (179, 1), (1526117, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_7, prime_t25_179, prime_t25_1526117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144415 : Nat.totient 26771144415 = 14277099392 := by
  rw [← show ((([(3, 1), (5, 1), (21149, 1), (84389, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_5, prime_t25_21149, prime_t25_84389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144416 : Nat.totient 26771144416 = 13385572192 := by
  rw [← show ((([(2, 5), (836598263, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_lucas_836598263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144417 : Nat.totient 26771144417 = 25196371200 := by
  rw [← show ((([(17, 1), (1574773201, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_17, prime_lucas_1574773201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144418 : Nat.totient 26771144418 = 8870278392 := by
  rw [← show ((([(2, 1), (3, 2), (167, 1), (8905903, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_167, prime_t25_8905903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144419 : Nat.totient 26771144419 = 24476304384 := by
  rw [← show ((([(19, 1), (29, 1), (2437, 1), (19937, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_19, prime_t25_29, prime_t25_2437, prime_t25_19937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144420 : Nat.totient 26771144420 = 10515432960 := by
  rw [← show ((([(2, 2), (5, 1), (61, 1), (613, 1), (35797, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_5, prime_t25_61, prime_t25_613, prime_t25_35797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144421 : Nat.totient 26771144421 = 15272995584 := by
  rw [← show ((([(3, 1), (7, 1), (617, 1), (2066153, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_7, prime_t25_617, prime_t25_2066153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144422 : Nat.totient 26771144422 = 11567808000 := by
  rw [← show ((([(2, 1), (11, 1), (41, 1), (43, 1), (761, 1), (907, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_11, prime_t25_41, prime_t25_43, prime_t25_761, prime_t25_907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144423 : Nat.totient 26771144423 = 25607181600 := by
  rw [← show ((([(23, 1), (1163962801, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_23, prime_lucas_1163962801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144424 : Nat.totient 26771144424 = 8635852800 := by
  rw [← show ((([(2, 3), (3, 1), (31, 1), (35982721, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_31, prime_lucas_35982721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144425 : Nat.totient 26771144425 = 21320871120 := by
  rw [← show ((([(5, 2), (223, 1), (4801999, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_5, prime_t25_223, prime_t25_4801999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144426 : Nat.totient 26771144426 = 12355912800 := by
  rw [← show ((([(2, 1), (13, 1), (1029659401, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_13, prime_lucas_1029659401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144427 : Nat.totient 26771144427 = 17760450048 := by
  rw [← show ((([(3, 2), (269, 1), (929, 1), (11903, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_269, prime_t25_929, prime_t25_11903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144428 : Nat.totient 26771144428 = 11163256704 := by
  rw [← show ((([(2, 2), (7, 1), (37, 1), (25840873, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_7, prime_t25_37, prime_t25_25840873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144429 : Nat.totient 26771144429 = 26771144428 := by
  rw [← show ((([(26771144429, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_26771144429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144430 : Nat.totient 26771144430 = 7138971840 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (892371481, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_5, prime_lucas_892371481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144431 : Nat.totient 26771144431 = 26769731832 := by
  rw [← show ((([(19213, 1), (1393387, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_19213, prime_t25_1393387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144432 : Nat.totient 26771144432 = 13384871808 := by
  rw [← show ((([(2, 4), (28183, 1), (59369, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_28183, prime_t25_59369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144433 : Nat.totient 26771144433 = 16223770640 := by
  rw [← show ((([(3, 1), (11, 1), (23003, 1), (35267, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_11, prime_t25_23003, prime_t25_35267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144434 : Nat.totient 26771144434 = 12428332800 := by
  rw [← show ((([(2, 1), (17, 1), (79, 1), (1451, 1), (6869, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_17, prime_t25_79, prime_t25_1451, prime_t25_6869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144435 : Nat.totient 26771144435 = 18276451200 := by
  rw [← show ((([(5, 1), (7, 1), (379, 1), (701, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_5, prime_t25_7, prime_t25_379, prime_t25_701, prime_t25_2879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144436 : Nat.totient 26771144436 = 8788824000 := by
  rw [← show ((([(2, 2), (3, 4), (101, 1), (199, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_101, prime_t25_199, prime_t25_4111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144437 : Nat.totient 26771144437 = 26766196960 := by
  rw [← show ((([(5417, 1), (4942061, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_5417, prime_t25_4942061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_26771144438 : Nat.totient 26771144438 = 12507353856 := by
  rw [← show ((([(2, 1), (19, 1), (73, 1), (9650737, 1)] : List FactorBlock).map factorBlockValue).prod) = 26771144438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_19, prime_t25_73, prime_t25_9650737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288801 : Nat.totient 53542288801 = 52297119252 := by
  rw [← show ((([(43, 1), (1245169507, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_43, prime_lucas_1245169507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288802 : Nat.totient 53542288802 = 26771144400 := by
  rw [← show ((([(2, 1), (26771144401, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_lucas_26771144401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288803 : Nat.totient 53542288803 = 34307020800 := by
  rw [← show ((([(3, 1), (41, 1), (73, 1), (997, 1), (5981, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_41, prime_t25_73, prime_t25_997, prime_t25_5981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288804 : Nat.totient 53542288804 = 26771144400 := by
  rw [← show ((([(2, 2), (13385572201, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_lucas_13385572201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288805 : Nat.totient 53542288805 = 42833831040 := by
  rw [← show ((([(5, 1), (10708457761, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_5, prime_lucas_10708457761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288806 : Nat.totient 53542288806 = 17847429600 := by
  rw [← show ((([(2, 1), (3, 1), (8923714801, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_lucas_8923714801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288807 : Nat.totient 53542288807 = 45701366424 := by
  rw [← show ((([(7, 1), (239, 1), (32003759, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_7, prime_t25_239, prime_t25_32003759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288808 : Nat.totient 53542288808 = 26770404400 := by
  rw [← show ((([(2, 3), (49331, 1), (135671, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_49331, prime_t25_135671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288809 : Nat.totient 53542288809 = 34464001824 := by
  rw [← show ((([(3, 2), (29, 1), (205142869, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_29, prime_lucas_205142869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288810 : Nat.totient 53542288810 = 21413672656 := by
  rw [← show ((([(2, 1), (5, 1), (6659, 1), (804059, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_5, prime_t25_6659, prime_t25_804059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288811 : Nat.totient 53542288811 = 48088363720 := by
  rw [← show ((([(11, 1), (83, 1), (58644347, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_11, prime_t25_83, prime_lucas_58644347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288812 : Nat.totient 53542288812 = 17847429600 := by
  rw [← show ((([(2, 2), (3, 1), (4461857401, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_lucas_4461857401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288813 : Nat.totient 53542288813 = 48685974480 := by
  rw [← show ((([(13, 2), (67, 1), (4728631, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_13, prime_t25_67, prime_t25_4728631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288814 : Nat.totient 53542288814 = 22946695200 := by
  rw [← show ((([(2, 1), (7, 1), (3824449201, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_7, prime_lucas_3824449201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288815 : Nat.totient 53542288815 = 28555887360 := by
  rw [← show ((([(3, 1), (5, 1), (3569485921, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_5, prime_lucas_3569485921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288816 : Nat.totient 53542288816 = 26674391040 := by
  rw [← show ((([(2, 4), (353, 1), (1637, 1), (5791, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_353, prime_t25_1637, prime_t25_5791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288817 : Nat.totient 53542288817 = 48709589760 := by
  rw [← show ((([(17, 1), (31, 1), (853, 1), (119107, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_17, prime_t25_31, prime_t25_853, prime_t25_119107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288818 : Nat.totient 53542288818 = 17847429588 := by
  rw [← show ((([(2, 1), (3, 3), (991523867, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_lucas_991523867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288819 : Nat.totient 53542288819 = 49327709184 := by
  rw [← show ((([(19, 1), (37, 1), (2029, 1), (37537, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_19, prime_t25_37, prime_t25_2029, prime_t25_37537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288820 : Nat.totient 53542288820 = 21416915520 := by
  rw [← show ((([(2, 2), (5, 1), (2677114441, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_5, prime_lucas_2677114441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288821 : Nat.totient 53542288821 = 30595593600 := by
  rw [← show ((([(3, 1), (7, 1), (2549632801, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_7, prime_lucas_2549632801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288822 : Nat.totient 53542288822 = 24151621000 := by
  rw [← show ((([(2, 1), (11, 1), (131, 1), (18578171, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_11, prime_t25_131, prime_t25_18578171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288823 : Nat.totient 53542288823 = 50468352000 := by
  rw [← show ((([(23, 1), (97, 1), (233, 1), (103001, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_23, prime_t25_97, prime_t25_233, prime_t25_103001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288824 : Nat.totient 53542288824 = 17560515840 := by
  rw [← show ((([(2, 3), (3, 1), (71, 1), (499, 1), (62969, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_71, prime_t25_499, prime_t25_62969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288825 : Nat.totient 53542288825 = 42829814160 := by
  rw [← show ((([(5, 2), (11299, 1), (189547, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_5, prime_t25_11299, prime_t25_189547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288826 : Nat.totient 53542288826 = 24711825600 := by
  rw [← show ((([(2, 1), (13, 1), (2059318801, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_13, prime_lucas_2059318801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288827 : Nat.totient 53542288827 = 35488529520 := by
  rw [← show ((([(3, 2), (173, 1), (34388111, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_173, prime_lucas_34388111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288828 : Nat.totient 53542288828 = 22818486432 := by
  rw [← show ((([(2, 2), (7, 2), (179, 1), (1526117, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_7, prime_t25_179, prime_t25_1526117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288829 : Nat.totient 53542288829 = 53542288828 := by
  rw [← show ((([(53542288829, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_53542288829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288830 : Nat.totient 53542288830 = 14277099392 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (21149, 1), (84389, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_5, prime_t25_21149, prime_t25_84389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288831 : Nat.totient 53542288831 = 53051075064 := by
  rw [← show ((([(109, 1), (491213659, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_109, prime_lucas_491213659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288832 : Nat.totient 53542288832 = 26771144384 := by
  rw [← show ((([(2, 6), (836598263, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_lucas_836598263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288833 : Nat.totient 53542288833 = 32449872000 := by
  rw [← show ((([(3, 1), (11, 1), (1622493601, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_3, prime_t25_11, prime_lucas_1622493601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288834 : Nat.totient 53542288834 = 25196371200 := by
  rw [← show ((([(2, 1), (17, 1), (1574773201, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_17, prime_lucas_1574773201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288835 : Nat.totient 53542288835 = 36700933248 := by
  rw [← show ((([(5, 1), (7, 1), (2677, 1), (571453, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_5, prime_t25_7, prime_t25_2677, prime_t25_571453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288836 : Nat.totient 53542288836 = 17740556784 := by
  rw [← show ((([(2, 2), (3, 2), (167, 1), (8905903, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_3, prime_t25_167, prime_t25_8905903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288837 : Nat.totient 53542288837 = 53501321740 := by
  rw [← show ((([(1307, 1), (40965791, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_1307, prime_lucas_40965791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t25_53542288838 : Nat.totient 53542288838 = 24476304384 := by
  rw [← show ((([(2, 1), (19, 1), (29, 1), (2437, 1), (19937, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542288838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t25_2, prime_t25_19, prime_t25_29, prime_t25_2437, prime_t25_19937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The fifteenth finite diagonal certificate -/

theorem certifiedKill_diagonal_t25 :
    certifiedKill (periodLcm 25) (periodLcm 25) 38 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t25_26771144401, phi_t25_26771144402, phi_t25_26771144403, phi_t25_26771144404, phi_t25_26771144405, phi_t25_26771144406, phi_t25_26771144407, phi_t25_26771144408, phi_t25_26771144409, phi_t25_26771144410, phi_t25_26771144411, phi_t25_26771144412, phi_t25_26771144413, phi_t25_26771144414, phi_t25_26771144415, phi_t25_26771144416, phi_t25_26771144417, phi_t25_26771144418, phi_t25_26771144419, phi_t25_26771144420, phi_t25_26771144421, phi_t25_26771144422, phi_t25_26771144423, phi_t25_26771144424, phi_t25_26771144425, phi_t25_26771144426, phi_t25_26771144427, phi_t25_26771144428, phi_t25_26771144429, phi_t25_26771144430, phi_t25_26771144431, phi_t25_26771144432, phi_t25_26771144433, phi_t25_26771144434, phi_t25_26771144435, phi_t25_26771144436, phi_t25_26771144437, phi_t25_26771144438, phi_t25_53542288801, phi_t25_53542288802, phi_t25_53542288803, phi_t25_53542288804, phi_t25_53542288805, phi_t25_53542288806, phi_t25_53542288807, phi_t25_53542288808, phi_t25_53542288809, phi_t25_53542288810, phi_t25_53542288811, phi_t25_53542288812, phi_t25_53542288813, phi_t25_53542288814, phi_t25_53542288815, phi_t25_53542288816, phi_t25_53542288817, phi_t25_53542288818, phi_t25_53542288819, phi_t25_53542288820, phi_t25_53542288821, phi_t25_53542288822, phi_t25_53542288823, phi_t25_53542288824, phi_t25_53542288825, phi_t25_53542288826, phi_t25_53542288827, phi_t25_53542288828, phi_t25_53542288829, phi_t25_53542288830, phi_t25_53542288831, phi_t25_53542288832, phi_t25_53542288833, phi_t25_53542288834, phi_t25_53542288835, phi_t25_53542288836, phi_t25_53542288837, phi_t25_53542288838]

/-- The fourteen-scale prefix through t=23 plus the t=25 extension all fire. -/
theorem certifiedKill_diagonal_all_imported_through_t25 :
    (((∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t)) ∧
      certifiedKill (periodLcm 19) (periodLcm 19) 32) ∧
      certifiedKill (periodLcm 23) (periodLcm 23) 35) ∧
      certifiedKill (periodLcm 25) (periodLcm 25) 38 :=
  ⟨certifiedKill_diagonal_all_imported_through_t23, certifiedKill_diagonal_t25⟩

#print axioms certifiedKill_diagonal_all_imported_through_t25

end TotientTailPeriodKiller
end Erdos249257
