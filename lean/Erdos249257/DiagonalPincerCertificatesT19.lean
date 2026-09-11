import Erdos249257.DiagonalPincerPrimeCertificates.Prime35814241
import Erdos249257.DiagonalPincerPrimeCertificates.Prime46558513
import Erdos249257.DiagonalPincerPrimeCertificates.Prime46558517
import Erdos249257.DiagonalPincerPrimeCertificates.Prime232792561
import Erdos249257.DiagonalPincerPrimeCertificates.Prime465585143
import Erdos249257.DiagonalPincerPrimeCertificates.Prime465585151

/-!
# The t=19 diagonal-pincer certificate

This generated extension consumes six isolated Lucas certificates,
reconstructs all 64 Euler totients in the t=19 window, and proves the
thirteenth finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=19 window -/

private theorem prime_t19_2 : Nat.Prime 2 := by norm_num
private theorem prime_t19_3 : Nat.Prime 3 := by norm_num
private theorem prime_t19_5 : Nat.Prime 5 := by norm_num
private theorem prime_t19_7 : Nat.Prime 7 := by norm_num
private theorem prime_t19_11 : Nat.Prime 11 := by norm_num
private theorem prime_t19_13 : Nat.Prime 13 := by norm_num
private theorem prime_t19_17 : Nat.Prime 17 := by norm_num
private theorem prime_t19_19 : Nat.Prime 19 := by norm_num
private theorem prime_t19_23 : Nat.Prime 23 := by norm_num
private theorem prime_t19_29 : Nat.Prime 29 := by norm_num
private theorem prime_t19_31 : Nat.Prime 31 := by norm_num
private theorem prime_t19_37 : Nat.Prime 37 := by norm_num
private theorem prime_t19_41 : Nat.Prime 41 := by norm_num
private theorem prime_t19_43 : Nat.Prime 43 := by norm_num
private theorem prime_t19_47 : Nat.Prime 47 := by norm_num
private theorem prime_t19_53 : Nat.Prime 53 := by norm_num
private theorem prime_t19_59 : Nat.Prime 59 := by norm_num
private theorem prime_t19_61 : Nat.Prime 61 := by norm_num
private theorem prime_t19_67 : Nat.Prime 67 := by norm_num
private theorem prime_t19_71 : Nat.Prime 71 := by norm_num
private theorem prime_t19_83 : Nat.Prime 83 := by norm_num
private theorem prime_t19_89 : Nat.Prime 89 := by norm_num
private theorem prime_t19_101 : Nat.Prime 101 := by norm_num
private theorem prime_t19_103 : Nat.Prime 103 := by norm_num
private theorem prime_t19_107 : Nat.Prime 107 := by norm_num
private theorem prime_t19_131 : Nat.Prime 131 := by norm_num
private theorem prime_t19_137 : Nat.Prime 137 := by norm_num
private theorem prime_t19_167 : Nat.Prime 167 := by norm_num
private theorem prime_t19_199 : Nat.Prime 199 := by norm_num
private theorem prime_t19_227 : Nat.Prime 227 := by norm_num
private theorem prime_t19_239 : Nat.Prime 239 := by norm_num
private theorem prime_t19_307 : Nat.Prime 307 := by norm_num
private theorem prime_t19_347 : Nat.Prime 347 := by norm_num
private theorem prime_t19_383 : Nat.Prime 383 := by norm_num
private theorem prime_t19_409 : Nat.Prime 409 := by norm_num
private theorem prime_t19_431 : Nat.Prime 431 := by norm_num
private theorem prime_t19_449 : Nat.Prime 449 := by norm_num
private theorem prime_t19_479 : Nat.Prime 479 := by norm_num
private theorem prime_t19_487 : Nat.Prime 487 := by norm_num
private theorem prime_t19_541 : Nat.Prime 541 := by norm_num
private theorem prime_t19_557 : Nat.Prime 557 := by norm_num
private theorem prime_t19_613 : Nat.Prime 613 := by norm_num
private theorem prime_t19_761 : Nat.Prime 761 := by norm_num
private theorem prime_t19_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_t19_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_t19_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_t19_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_t19_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_t19_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_t19_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_t19_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_t19_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_t19_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_t19_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_t19_3527 : Nat.Prime 3527 := by norm_num
private theorem prime_t19_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_t19_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_t19_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_t19_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_t19_7237 : Nat.Prime 7237 := by norm_num
private theorem prime_t19_7589 : Nat.Prime 7589 := by norm_num
private theorem prime_t19_9931 : Nat.Prime 9931 := by norm_num
private theorem prime_t19_13933 : Nat.Prime 13933 := by norm_num
private theorem prime_t19_20341 : Nat.Prime 20341 := by norm_num
private theorem prime_t19_20897 : Nat.Prime 20897 := by norm_num
private theorem prime_t19_24551 : Nat.Prime 24551 := by norm_num
private theorem prime_t19_27953 : Nat.Prime 27953 := by norm_num
private theorem prime_t19_39161 : Nat.Prime 39161 := by norm_num
private theorem prime_t19_39443 : Nat.Prime 39443 := by norm_num
private theorem prime_t19_54163 : Nat.Prime 54163 := by norm_num
private theorem prime_t19_59167 : Nat.Prime 59167 := by norm_num
private theorem prime_t19_84391 : Nat.Prime 84391 := by norm_num
private theorem prime_t19_93491 : Nat.Prime 93491 := by norm_num
private theorem prime_t19_105527 : Nat.Prime 105527 := by norm_num
private theorem prime_t19_135581 : Nat.Prime 135581 := by norm_num
private theorem prime_t19_161999 : Nat.Prime 161999 := by norm_num
private theorem prime_t19_279967 : Nat.Prime 279967 := by norm_num
private theorem prime_t19_289543 : Nat.Prime 289543 := by norm_num
private theorem prime_t19_349801 : Nat.Prime 349801 := by norm_num
private theorem prime_t19_376687 : Nat.Prime 376687 := by norm_num
private theorem prime_t19_417191 : Nat.Prime 417191 := by norm_num
private theorem prime_t19_454673 : Nat.Prime 454673 := by norm_num
private theorem prime_t19_802733 : Nat.Prime 802733 := by norm_num
private theorem prime_t19_898813 : Nat.Prime 898813 := by norm_num
private theorem prime_t19_1265177 : Nat.Prime 1265177 := by norm_num
private theorem prime_t19_4392313 : Nat.Prime 4392313 := by norm_num
private theorem prime_t19_8621947 : Nat.Prime 8621947 := by norm_num
private theorem prime_t19_10121417 : Nat.Prime 10121417 := by norm_num
private theorem prime_t19_17907121 : Nat.Prime 17907121 := by norm_num
private theorem prime_t19_25865843 : Nat.Prime 25865843 := by norm_num
private theorem prime_t19_27387361 : Nat.Prime 27387361 := by norm_num

/-! ## Exact t=19 window totients -/

private theorem phi_t19_232792561 : Nat.totient 232792561 = 232792560 := by
  rw [← show ((([(232792561, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792561 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_232792561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792562 : Nat.totient 232792562 = 116289652 := by
  rw [← show ((([(2, 1), (1103, 1), (105527, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792562 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_1103, prime_t19_105527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792563 : Nat.totient 232792563 = 154870088 := by
  rw [← show ((([(3, 1), (479, 1), (161999, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792563 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_479, prime_t19_161999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792564 : Nat.totient 232792564 = 116360064 := by
  rw [← show ((([(2, 2), (4177, 1), (13933, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792564 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_4177, prime_t19_13933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792565 : Nat.totient 232792565 = 186234048 := by
  rw [← show ((([(5, 1), (46558513, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792565 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_5, prime_lucas_46558513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792566 : Nat.totient 232792566 = 76843944 := by
  rw [← show ((([(2, 1), (3, 1), (103, 1), (376687, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792566 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_103, prime_t19_376687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792567 : Nat.totient 232792567 = 194143392 := by
  rw [← show ((([(7, 1), (37, 1), (898813, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792567 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_7, prime_t19_37, prime_t19_898813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792568 : Nat.totient 232792568 = 111335488 := by
  rw [← show ((([(2, 3), (23, 1), (1265177, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792568 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_23, prime_t19_1265177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792569 : Nat.totient 232792569 = 155195028 := by
  rw [← show ((([(3, 3), (8621947, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792569 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_8621947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792570 : Nat.totient 232792570 = 89905984 := by
  rw [← show ((([(2, 1), (5, 1), (29, 1), (802733, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792570 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_5, prime_t19_29, prime_t19_802733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792571 : Nat.totient 232792571 = 211509000 := by
  rw [← show ((([(11, 1), (2131, 1), (9931, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792571 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_11, prime_t19_2131, prime_t19_9931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792572 : Nat.totient 232792572 = 76439088 := by
  rw [← show ((([(2, 2), (3, 1), (67, 1), (289543, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792572 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_67, prime_t19_289543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792573 : Nat.totient 232792573 = 214885440 := by
  rw [← show ((([(13, 1), (17907121, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792573 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_13, prime_t19_17907121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792574 : Nat.totient 232792574 = 99441432 := by
  rw [← show ((([(2, 1), (7, 1), (307, 1), (54163, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792574 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_7, prime_t19_307, prime_t19_54163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792575 : Nat.totient 232792575 = 123836160 := by
  rw [← show ((([(3, 1), (5, 2), (409, 1), (7589, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792575 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_5, prime_t19_409, prime_t19_7589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792576 : Nat.totient 232792576 = 116396032 := by
  rw [← show ((([(2, 9), (454673, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792576 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_454673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792577 : Nat.totient 232792577 = 216928000 := by
  rw [← show ((([(17, 1), (101, 1), (135581, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792577 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_17, prime_t19_101, prime_t19_135581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792578 : Nat.totient 232792578 = 75094200 := by
  rw [← show ((([(2, 1), (3, 2), (31, 1), (417191, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792578 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_31, prime_t19_417191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792579 : Nat.totient 232792579 = 220379616 := by
  rw [← show ((([(19, 1), (1693, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792579 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_19, prime_t19_1693, prime_t19_7237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792580 : Nat.totient 232792580 = 92945408 := by
  rw [← show ((([(2, 2), (5, 1), (557, 1), (20897, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792580 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_5, prime_t19_557, prime_t19_20897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792581 : Nat.totient 232792581 = 132690432 := by
  rw [← show ((([(3, 1), (7, 2), (449, 1), (3527, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792581 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_7, prime_t19_449, prime_t19_3527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792582 : Nat.totient 232792582 = 105565000 := by
  rw [← show ((([(2, 1), (11, 1), (431, 1), (24551, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792582 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_11, prime_t19_431, prime_t19_24551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792583 : Nat.totient 232792583 = 220799040 := by
  rw [← show ((([(43, 1), (59, 1), (89, 1), (1031, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792583 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_43, prime_t19_59, prime_t19_89, prime_t19_1031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792584 : Nat.totient 232792584 = 77371136 := by
  rw [← show ((([(2, 3), (3, 1), (347, 1), (27953, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792584 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_347, prime_t19_27953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792585 : Nat.totient 232792585 = 186234064 := by
  rw [← show ((([(5, 1), (46558517, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792585 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_5, prime_lucas_46558517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792586 : Nat.totient 232792586 = 106966704 := by
  rw [← show ((([(2, 1), (13, 1), (227, 1), (39443, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792586 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_13, prime_t19_227, prime_t19_39443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792587 : Nat.totient 232792587 = 155195052 := by
  rw [← show ((([(3, 2), (25865843, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792587 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_25865843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792588 : Nat.totient 232792588 = 96750720 := by
  rw [← show ((([(2, 2), (7, 1), (41, 1), (199, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792588 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_7, prime_t19_41, prime_t19_199, prime_t19_1019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792589 : Nat.totient 232792589 = 228400224 := by
  rw [← show ((([(53, 1), (4392313, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792589 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_53, prime_t19_4392313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792590 : Nat.totient 232792590 = 61329440 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (83, 1), (93491, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792590 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_5, prime_t19_83, prime_t19_93491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792591 : Nat.totient 232792591 = 222671152 := by
  rw [← show ((([(23, 1), (10121417, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792591 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_23, prime_t19_10121417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_232792592 : Nat.totient 232792592 = 113587200 := by
  rw [← show ((([(2, 4), (61, 1), (137, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 232792592 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_61, prime_t19_137, prime_t19_1741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585121 : Nat.totient 465585121 = 465303492 := by
  rw [← show ((([(1663, 1), (279967, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585121 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_1663, prime_t19_279967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585122 : Nat.totient 465585122 = 232792560 := by
  rw [← show ((([(2, 1), (232792561, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585122 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_lucas_232792561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585123 : Nat.totient 465585123 = 298196640 := by
  rw [← show ((([(3, 1), (43, 1), (61, 1), (59167, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585123 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_43, prime_t19_61, prime_t19_59167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585124 : Nat.totient 465585124 = 232579304 := by
  rw [← show ((([(2, 2), (1103, 1), (105527, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585124 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_1103, prime_t19_105527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585125 : Nat.totient 465585125 = 353496000 := by
  rw [← show ((([(5, 3), (31, 1), (53, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585125 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_5, prime_t19_31, prime_t19_53, prime_t19_2267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585126 : Nat.totient 465585126 = 154870088 := by
  rw [← show ((([(2, 1), (3, 1), (479, 1), (161999, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585126 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_479, prime_t19_161999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585127 : Nat.totient 465585127 = 392616000 := by
  rw [← show ((([(7, 1), (71, 1), (761, 1), (1231, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585127 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_7, prime_t19_71, prime_t19_761, prime_t19_1231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585128 : Nat.totient 465585128 = 232720128 := by
  rw [← show ((([(2, 3), (4177, 1), (13933, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585128 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_4177, prime_t19_13933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585129 : Nat.totient 465585129 = 310147200 := by
  rw [← show ((([(3, 2), (1321, 1), (39161, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585129 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_1321, prime_t19_39161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585130 : Nat.totient 465585130 = 186234048 := by
  rw [← show ((([(2, 1), (5, 1), (46558513, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585130 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_5, prime_lucas_46558513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585131 : Nat.totient 465585131 = 423258000 := by
  rw [← show ((([(11, 3), (349801, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585131 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_11, prime_t19_349801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585132 : Nat.totient 465585132 = 153687888 := by
  rw [← show ((([(2, 2), (3, 1), (103, 1), (376687, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585132 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_103, prime_t19_376687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585133 : Nat.totient 465585133 = 429770880 := by
  rw [← show ((([(13, 1), (35814241, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585133 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_13, prime_lucas_35814241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585134 : Nat.totient 465585134 = 194143392 := by
  rw [← show ((([(2, 1), (7, 1), (37, 1), (898813, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585134 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_7, prime_t19_37, prime_t19_898813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585135 : Nat.totient 465585135 = 240364800 := by
  rw [← show ((([(3, 1), (5, 1), (41, 1), (131, 1), (5779, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585135 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_5, prime_t19_41, prime_t19_131, prime_t19_5779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585136 : Nat.totient 465585136 = 222670976 := by
  rw [← show ((([(2, 4), (23, 1), (1265177, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585136 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_23, prime_t19_1265177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585137 : Nat.totient 465585137 = 438197760 := by
  rw [← show ((([(17, 1), (27387361, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585137 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_17, prime_t19_27387361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585138 : Nat.totient 465585138 = 155195028 := by
  rw [← show ((([(2, 1), (3, 3), (8621947, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585138 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_8621947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585139 : Nat.totient 465585139 = 440901216 := by
  rw [← show ((([(19, 1), (4397, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585139 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_19, prime_t19_4397, prime_t19_5573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585140 : Nat.totient 465585140 = 179811968 := by
  rw [← show ((([(2, 2), (5, 1), (29, 1), (802733, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585140 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_5, prime_t19_29, prime_t19_802733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585141 : Nat.totient 465585141 = 262388160 := by
  rw [← show ((([(3, 1), (7, 1), (107, 1), (383, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585141 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_7, prime_t19_107, prime_t19_383, prime_t19_541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585142 : Nat.totient 465585142 = 211509000 := by
  rw [← show ((([(2, 1), (11, 1), (2131, 1), (9931, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585142 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_11, prime_t19_2131, prime_t19_9931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585143 : Nat.totient 465585143 = 465585142 := by
  rw [← show ((([(465585143, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585143 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_465585143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585144 : Nat.totient 465585144 = 152878176 := by
  rw [← show ((([(2, 3), (3, 1), (67, 1), (289543, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585144 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_67, prime_t19_289543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585145 : Nat.totient 465585145 = 368530624 := by
  rw [← show ((([(5, 1), (167, 1), (239, 1), (2333, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585145 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_5, prime_t19_167, prime_t19_239, prime_t19_2333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585146 : Nat.totient 465585146 = 214885440 := by
  rw [← show ((([(2, 1), (13, 1), (17907121, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585146 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_13, prime_t19_17907121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585147 : Nat.totient 465585147 = 309880080 := by
  rw [← show ((([(3, 2), (613, 1), (84391, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585147 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_3, prime_t19_613, prime_t19_84391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585148 : Nat.totient 465585148 = 198882864 := by
  rw [← show ((([(2, 2), (7, 1), (307, 1), (54163, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585148 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_7, prime_t19_307, prime_t19_54163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585149 : Nat.totient 465585149 = 454721040 := by
  rw [← show ((([(47, 1), (487, 1), (20341, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585149 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_47, prime_t19_487, prime_t19_20341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585150 : Nat.totient 465585150 = 123836160 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (409, 1), (7589, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585150 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_3, prime_t19_5, prime_t19_409, prime_t19_7589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585151 : Nat.totient 465585151 = 465585150 := by
  rw [← show ((([(465585151, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585151 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_465585151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t19_465585152 : Nat.totient 465585152 = 232792064 := by
  rw [← show ((([(2, 10), (454673, 1)] : List FactorBlock).map factorBlockValue).prod) = 465585152 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t19_2, prime_t19_454673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The thirteenth finite diagonal certificate -/

theorem certifiedKill_diagonal_t19 :
    certifiedKill (periodLcm 19) (periodLcm 19) 32 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t19_232792561, phi_t19_232792562, phi_t19_232792563, phi_t19_232792564, phi_t19_232792565, phi_t19_232792566, phi_t19_232792567, phi_t19_232792568, phi_t19_232792569, phi_t19_232792570, phi_t19_232792571, phi_t19_232792572, phi_t19_232792573, phi_t19_232792574, phi_t19_232792575, phi_t19_232792576, phi_t19_232792577, phi_t19_232792578, phi_t19_232792579, phi_t19_232792580, phi_t19_232792581, phi_t19_232792582, phi_t19_232792583, phi_t19_232792584, phi_t19_232792585, phi_t19_232792586, phi_t19_232792587, phi_t19_232792588, phi_t19_232792589, phi_t19_232792590, phi_t19_232792591, phi_t19_232792592, phi_t19_465585121, phi_t19_465585122, phi_t19_465585123, phi_t19_465585124, phi_t19_465585125, phi_t19_465585126, phi_t19_465585127, phi_t19_465585128, phi_t19_465585129, phi_t19_465585130, phi_t19_465585131, phi_t19_465585132, phi_t19_465585133, phi_t19_465585134, phi_t19_465585135, phi_t19_465585136, phi_t19_465585137, phi_t19_465585138, phi_t19_465585139, phi_t19_465585140, phi_t19_465585141, phi_t19_465585142, phi_t19_465585143, phi_t19_465585144, phi_t19_465585145, phi_t19_465585146, phi_t19_465585147, phi_t19_465585148, phi_t19_465585149, phi_t19_465585150, phi_t19_465585151, phi_t19_465585152]

/-- The twelve-scale base prefix plus the t=19 extension all fire. -/
theorem certifiedKill_diagonal_all_imported_through_t19 :
    (∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t)) ∧
      certifiedKill (periodLcm 19) (periodLcm 19) 32 :=
  ⟨certifiedKill_diagonal_all_imported, certifiedKill_diagonal_t19⟩

#print axioms certifiedKill_diagonal_all_imported_through_t19

end TotientTailPeriodKiller
end Erdos249257
