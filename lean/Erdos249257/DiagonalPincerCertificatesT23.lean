import Erdos249257.DiagonalPincerCertificatesT19
import Erdos249257.DiagonalPincerPrimeCertificates.Prime43707991
import Erdos249257.DiagonalPincerPrimeCertificates.Prime70916939
import Erdos249257.DiagonalPincerPrimeCertificates.Prime73851433
import Erdos249257.DiagonalPincerPrimeCertificates.Prime99152387
import Erdos249257.DiagonalPincerPrimeCertificates.Prime101023187
import Erdos249257.DiagonalPincerPrimeCertificates.Prime162249361
import Erdos249257.DiagonalPincerPrimeCertificates.Prime254963281
import Erdos249257.DiagonalPincerPrimeCertificates.Prime314954641
import Erdos249257.DiagonalPincerPrimeCertificates.Prime334639307
import Erdos249257.DiagonalPincerPrimeCertificates.Prime509926561
import Erdos249257.DiagonalPincerPrimeCertificates.Prime823727521
import Erdos249257.DiagonalPincerPrimeCertificates.Prime892371481
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1070845781
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2677114441
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3569485921
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10708457761
import Erdos249257.DiagonalPincerPrimeCertificates.Prime10708457791

/-!
# The t=23 diagonal-pincer certificate

This generated extension consumes seventeen new isolated Lucas certificates
plus the reused t=19 certificate for 232792561, reconstructs all 70 Euler
totients in the t=23 window, and proves the fourteenth finite diagonal kill
without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=23 window -/

private theorem prime_t23_2 : Nat.Prime 2 := by norm_num
private theorem prime_t23_3 : Nat.Prime 3 := by norm_num
private theorem prime_t23_5 : Nat.Prime 5 := by norm_num
private theorem prime_t23_7 : Nat.Prime 7 := by norm_num
private theorem prime_t23_11 : Nat.Prime 11 := by norm_num
private theorem prime_t23_13 : Nat.Prime 13 := by norm_num
private theorem prime_t23_17 : Nat.Prime 17 := by norm_num
private theorem prime_t23_19 : Nat.Prime 19 := by norm_num
private theorem prime_t23_23 : Nat.Prime 23 := by norm_num
private theorem prime_t23_29 : Nat.Prime 29 := by norm_num
private theorem prime_t23_31 : Nat.Prime 31 := by norm_num
private theorem prime_t23_37 : Nat.Prime 37 := by norm_num
private theorem prime_t23_41 : Nat.Prime 41 := by norm_num
private theorem prime_t23_43 : Nat.Prime 43 := by norm_num
private theorem prime_t23_47 : Nat.Prime 47 := by norm_num
private theorem prime_t23_53 : Nat.Prime 53 := by norm_num
private theorem prime_t23_61 : Nat.Prime 61 := by norm_num
private theorem prime_t23_67 : Nat.Prime 67 := by norm_num
private theorem prime_t23_71 : Nat.Prime 71 := by norm_num
private theorem prime_t23_83 : Nat.Prime 83 := by norm_num
private theorem prime_t23_97 : Nat.Prime 97 := by norm_num
private theorem prime_t23_103 : Nat.Prime 103 := by norm_num
private theorem prime_t23_109 : Nat.Prime 109 := by norm_num
private theorem prime_t23_113 : Nat.Prime 113 := by norm_num
private theorem prime_t23_151 : Nat.Prime 151 := by norm_num
private theorem prime_t23_163 : Nat.Prime 163 := by norm_num
private theorem prime_t23_173 : Nat.Prime 173 := by norm_num
private theorem prime_t23_191 : Nat.Prime 191 := by norm_num
private theorem prime_t23_223 : Nat.Prime 223 := by norm_num
private theorem prime_t23_307 : Nat.Prime 307 := by norm_num
private theorem prime_t23_317 : Nat.Prime 317 := by norm_num
private theorem prime_t23_379 : Nat.Prime 379 := by norm_num
private theorem prime_t23_449 : Nat.Prime 449 := by norm_num
private theorem prime_t23_457 : Nat.Prime 457 := by norm_num
private theorem prime_t23_599 : Nat.Prime 599 := by norm_num
private theorem prime_t23_613 : Nat.Prime 613 := by norm_num
private theorem prime_t23_661 : Nat.Prime 661 := by norm_num
private theorem prime_t23_701 : Nat.Prime 701 := by norm_num
private theorem prime_t23_743 : Nat.Prime 743 := by norm_num
private theorem prime_t23_811 : Nat.Prime 811 := by norm_num
private theorem prime_t23_863 : Nat.Prime 863 := by norm_num
private theorem prime_t23_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_t23_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_t23_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_t23_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_t23_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_t23_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_t23_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_t23_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_t23_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_t23_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_t23_4021 : Nat.Prime 4021 := by norm_num
private theorem prime_t23_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_t23_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_t23_4547 : Nat.Prime 4547 := by norm_num
private theorem prime_t23_4783 : Nat.Prime 4783 := by norm_num
private theorem prime_t23_5659 : Nat.Prime 5659 := by norm_num
private theorem prime_t23_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_t23_8117 : Nat.Prime 8117 := by norm_num
private theorem prime_t23_9161 : Nat.Prime 9161 := by norm_num
private theorem prime_t23_10903 : Nat.Prime 10903 := by norm_num
private theorem prime_t23_11299 : Nat.Prime 11299 := by norm_num
private theorem prime_t23_14639 : Nat.Prime 14639 := by norm_num
private theorem prime_t23_21149 : Nat.Prime 21149 := by norm_num
private theorem prime_t23_24083 : Nat.Prime 24083 := by norm_num
private theorem prime_t23_29567 : Nat.Prime 29567 := by norm_num
private theorem prime_t23_35797 : Nat.Prime 35797 := by norm_num
private theorem prime_t23_39251 : Nat.Prime 39251 := by norm_num
private theorem prime_t23_40639 : Nat.Prime 40639 := by norm_num
private theorem prime_t23_80701 : Nat.Prime 80701 := by norm_num
private theorem prime_t23_84389 : Nat.Prime 84389 := by norm_num
private theorem prime_t23_105953 : Nat.Prime 105953 := by norm_num
private theorem prime_t23_189547 : Nat.Prime 189547 := by norm_num
private theorem prime_t23_238363 : Nat.Prime 238363 := by norm_num
private theorem prime_t23_258871 : Nat.Prime 258871 := by norm_num
private theorem prime_t23_279967 : Nat.Prime 279967 := by norm_num
private theorem prime_t23_285757 : Nat.Prime 285757 := by norm_num
private theorem prime_t23_309493 : Nat.Prime 309493 := by norm_num
private theorem prime_t23_350729 : Nat.Prime 350729 := by norm_num
private theorem prime_t23_571453 : Nat.Prime 571453 := by norm_num
private theorem prime_t23_703763 : Nat.Prime 703763 := by norm_num
private theorem prime_t23_804059 : Nat.Prime 804059 := by norm_num
private theorem prime_t23_2481107 : Nat.Prime 2481107 := by norm_num
private theorem prime_t23_3508669 : Nat.Prime 3508669 := by norm_num
private theorem prime_t23_4068563 : Nat.Prime 4068563 := by norm_num
private theorem prime_t23_4801999 : Nat.Prime 4801999 := by norm_num
private theorem prime_t23_7938071 : Nat.Prime 7938071 := by norm_num
private theorem prime_t23_9989233 : Nat.Prime 9989233 := by norm_num
private theorem prime_t23_15363641 : Nat.Prime 15363641 := by norm_num
private theorem prime_t23_15701551 : Nat.Prime 15701551 := by norm_num

/-! ## Exact t=23 window totients -/

private theorem phi_t23_5354228881 : Nat.totient 5354228881 = 5353418164 := by
  rw [← show ((([(6659, 1), (804059, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_6659, prime_t23_804059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228882 : Nat.totient 5354228882 = 2677114440 := by
  rw [← show ((([(2, 1), (2677114441, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_lucas_2677114441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228883 : Nat.totient 5354228883 = 3569274848 := by
  rw [← show ((([(3, 1), (21149, 1), (84389, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_21149, prime_t23_84389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228884 : Nat.totient 5354228884 = 2628858240 := by
  rw [← show ((([(2, 2), (61, 1), (613, 1), (35797, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_61, prime_t23_613, prime_t23_35797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228885 : Nat.totient 5354228885 = 4264174224 := by
  rw [← show ((([(5, 1), (223, 1), (4801999, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_5, prime_t23_223, prime_t23_4801999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228886 : Nat.totient 5354228886 = 1784742960 := by
  rw [← show ((([(2, 1), (3, 1), (892371481, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_lucas_892371481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228887 : Nat.totient 5354228887 = 4569112800 := by
  rw [← show ((([(7, 1), (379, 1), (701, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_7, prime_t23_379, prime_t23_701, prime_t23_2879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228888 : Nat.totient 5354228888 = 2637157248 := by
  rw [← show ((([(2, 3), (67, 1), (9989233, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_67, prime_t23_9989233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228889 : Nat.totient 5354228889 = 3569154264 := by
  rw [← show ((([(3, 2), (14639, 1), (40639, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_14639, prime_t23_40639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228890 : Nat.totient 5354228890 = 2125206720 := by
  rw [← show ((([(2, 1), (5, 1), (163, 1), (743, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_5, prime_t23_163, prime_t23_743, prime_t23_4421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228891 : Nat.totient 5354228891 = 4710465000 := by
  rw [← show ((([(11, 1), (31, 1), (15701551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_11, prime_t23_31, prime_t23_15701551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228892 : Nat.totient 5354228892 = 1757022720 := by
  rw [← show ((([(2, 2), (3, 1), (97, 1), (191, 1), (24083, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_t23_97, prime_t23_191, prime_t23_24083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228893 : Nat.totient 5354228893 = 4696937280 := by
  rw [← show ((([(13, 1), (37, 1), (43, 1), (258871, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_13, prime_t23_37, prime_t23_43, prime_t23_258871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228894 : Nat.totient 5354228894 = 2273616864 := by
  rw [← show ((([(2, 1), (7, 1), (109, 1), (3508669, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_7, prime_t23_109, prime_t23_3508669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228895 : Nat.totient 5354228895 = 2840365440 := by
  rw [← show ((([(3, 1), (5, 1), (307, 1), (661, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_5, prime_t23_307, prime_t23_661, prime_t23_1759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228896 : Nat.totient 5354228896 = 2676550848 := by
  rw [← show ((([(2, 5), (5659, 1), (29567, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_5659, prime_t23_29567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228897 : Nat.totient 5354228897 = 5039274240 := by
  rw [← show ((([(17, 1), (314954641, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_17, prime_lucas_314954641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228898 : Nat.totient 5354228898 = 1784742948 := by
  rw [← show ((([(2, 1), (3, 3), (99152387, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_lucas_99152387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228899 : Nat.totient 5354228899 = 5068740960 := by
  rw [← show ((([(19, 2), (1619, 1), (9161, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_19, prime_t23_1619, prime_t23_9161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228900 : Nat.totient 5354228900 = 2129304960 := by
  rw [← show ((([(2, 2), (5, 2), (173, 1), (309493, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228900 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_5, prime_t23_173, prime_t23_309493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228901 : Nat.totient 5354228901 = 3059559360 := by
  rw [← show ((([(3, 1), (7, 1), (254963281, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228901 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_7, prime_lucas_254963281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228902 : Nat.totient 5354228902 = 2432657920 := by
  rw [← show ((([(2, 1), (11, 1), (2297, 1), (105953, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228902 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_11, prime_t23_2297, prime_t23_105953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228903 : Nat.totient 5354228903 = 5121436320 := by
  rw [← show ((([(23, 1), (232792561, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228903 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_23, prime_lucas_232792561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228904 : Nat.totient 5354228904 = 1779110336 := by
  rw [← show ((([(2, 3), (3, 1), (317, 1), (703763, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228904 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_t23_317, prime_t23_703763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228905 : Nat.totient 5354228905 = 4283383120 := by
  rw [← show ((([(5, 1), (1070845781, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228905 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_5, prime_lucas_1070845781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228906 : Nat.totient 5354228906 = 2441408304 := by
  rw [← show ((([(2, 1), (13, 1), (83, 1), (2481107, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228906 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_13, prime_t23_83, prime_t23_2481107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228907 : Nat.totient 5354228907 = 3444876288 := by
  rw [← show ((([(3, 2), (29, 1), (4289, 1), (4783, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228907 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_29, prime_t23_4289, prime_t23_4783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228908 : Nat.totient 5354228908 = 2245846224 := by
  rw [← show ((([(2, 2), (7, 1), (47, 1), (4068563, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228908 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_7, prime_t23_47, prime_t23_4068563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228909 : Nat.totient 5354228909 = 5212189440 := by
  rw [← show ((([(41, 1), (457, 1), (285757, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228909 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_41, prime_t23_457, prime_t23_285757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228910 : Nat.totient 5354228910 = 1427444000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (4547, 1), (39251, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228910 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_t23_5, prime_t23_4547, prime_t23_39251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228911 : Nat.totient 5354228911 = 5253205672 := by
  rw [← show ((([(53, 1), (101023187, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228911 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_53, prime_lucas_101023187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228912 : Nat.totient 5354228912 = 2677114448 := by
  rw [← show ((([(2, 4), (334639307, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228912 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_lucas_334639307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228913 : Nat.totient 5354228913 = 3244987200 := by
  rw [← show ((([(3, 1), (11, 1), (162249361, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228913 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_11, prime_lucas_162249361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228914 : Nat.totient 5354228914 = 2514018304 := by
  rw [← show ((([(2, 1), (17, 1), (449, 1), (350729, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228914 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_17, prime_t23_449, prime_t23_350729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_5354228915 : Nat.totient 5354228915 = 3629502720 := by
  rw [← show ((([(5, 1), (7, 1), (103, 1), (863, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354228915 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_5, prime_t23_7, prime_t23_103, prime_t23_863, prime_t23_1721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457761 : Nat.totient 10708457761 = 10708457760 := by
  rw [← show ((([(10708457761, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457761 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_10708457761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457762 : Nat.totient 10708457762 = 5353418164 := by
  rw [← show ((([(2, 1), (6659, 1), (804059, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457762 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_6659, prime_t23_804059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457763 : Nat.totient 10708457763 = 7138971840 := by
  rw [← show ((([(3, 1), (3569485921, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457763 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_lucas_3569485921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457764 : Nat.totient 10708457764 = 5354228880 := by
  rw [← show ((([(2, 2), (2677114441, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457764 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_lucas_2677114441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457765 : Nat.totient 10708457765 = 8565962832 := by
  rw [← show ((([(5, 1), (11299, 1), (189547, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457765 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_5, prime_t23_11299, prime_t23_189547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457766 : Nat.totient 10708457766 = 3569274848 := by
  rw [← show ((([(2, 1), (3, 1), (21149, 1), (84389, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457766 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_t23_21149, prime_t23_84389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457767 : Nat.totient 10708457767 = 9175233312 := by
  rw [← show ((([(7, 1), (2677, 1), (571453, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457767 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_7, prime_t23_2677, prime_t23_571453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457768 : Nat.totient 10708457768 = 5257716480 := by
  rw [← show ((([(2, 3), (61, 1), (613, 1), (35797, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457768 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_61, prime_t23_613, prime_t23_35797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457769 : Nat.totient 10708457769 = 6789758976 := by
  rw [← show ((([(3, 3), (47, 1), (53, 1), (113, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457769 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_47, prime_t23_53, prime_t23_113, prime_t23_1409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457770 : Nat.totient 10708457770 = 4264174224 := by
  rw [← show ((([(2, 1), (5, 1), (223, 1), (4801999, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457770 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_5, prime_t23_223, prime_t23_4801999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457771 : Nat.totient 10708457771 = 9732869520 := by
  rw [← show ((([(11, 2), (8117, 1), (10903, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457771 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_11, prime_t23_8117, prime_t23_10903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457772 : Nat.totient 10708457772 = 3569485920 := by
  rw [← show ((([(2, 2), (3, 1), (892371481, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457772 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_lucas_892371481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457773 : Nat.totient 10708457773 = 9884730240 := by
  rw [← show ((([(13, 1), (823727521, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457773 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_13, prime_lucas_823727521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457774 : Nat.totient 10708457774 = 4569112800 := by
  rw [← show ((([(2, 1), (7, 1), (379, 1), (701, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457774 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_7, prime_t23_379, prime_t23_701, prime_t23_2879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457775 : Nat.totient 10708457775 = 5701619040 := by
  rw [← show ((([(3, 1), (5, 2), (599, 1), (238363, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457775 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_5, prime_t23_599, prime_t23_238363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457776 : Nat.totient 10708457776 = 5274314496 := by
  rw [← show ((([(2, 4), (67, 1), (9989233, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457776 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_67, prime_t23_9989233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457777 : Nat.totient 10708457777 = 9832729600 := by
  rw [← show ((([(17, 1), (41, 1), (15363641, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457777 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_17, prime_t23_41, prime_t23_15363641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457778 : Nat.totient 10708457778 = 3569154264 := by
  rw [← show ((([(2, 1), (3, 2), (14639, 1), (40639, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457778 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_t23_14639, prime_t23_40639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457779 : Nat.totient 10708457779 = 10001968200 := by
  rw [← show ((([(19, 1), (71, 1), (7938071, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457779 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_19, prime_t23_71, prime_t23_7938071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457780 : Nat.totient 10708457780 = 4250413440 := by
  rw [← show ((([(2, 2), (5, 1), (163, 1), (743, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457780 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_5, prime_t23_163, prime_t23_743, prime_t23_4421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457781 : Nat.totient 10708457781 = 6119118720 := by
  rw [← show ((([(3, 1), (7, 1), (509926561, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457781 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_7, prime_lucas_509926561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457782 : Nat.totient 10708457782 = 4710465000 := by
  rw [← show ((([(2, 1), (11, 1), (31, 1), (15701551, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457782 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_11, prime_t23_31, prime_t23_15701551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457783 : Nat.totient 10708457783 = 10236676824 := by
  rw [← show ((([(23, 1), (1663, 1), (279967, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457783 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_23, prime_t23_1663, prime_t23_279967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457784 : Nat.totient 10708457784 = 3514045440 := by
  rw [← show ((([(2, 3), (3, 1), (97, 1), (191, 1), (24083, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457784 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_t23_97, prime_t23_191, prime_t23_24083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457785 : Nat.totient 10708457785 = 8271360384 := by
  rw [← show ((([(5, 1), (29, 1), (73851433, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457785 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_5, prime_t23_29, prime_lucas_73851433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457786 : Nat.totient 10708457786 = 4696937280 := by
  rw [← show ((([(2, 1), (13, 1), (37, 1), (43, 1), (258871, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457786 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_13, prime_t23_37, prime_t23_43, prime_t23_258871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457787 : Nat.totient 10708457787 = 7118247600 := by
  rw [← show ((([(3, 2), (811, 1), (1031, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457787 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_811, prime_t23_1031, prime_t23_1423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457788 : Nat.totient 10708457788 = 4547233728 := by
  rw [← show ((([(2, 2), (7, 1), (109, 1), (3508669, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457788 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_7, prime_t23_109, prime_t23_3508669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457789 : Nat.totient 10708457789 = 10637540700 := by
  rw [← show ((([(151, 1), (70916939, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457789 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_151, prime_lucas_70916939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457790 : Nat.totient 10708457790 = 2840365440 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (307, 1), (661, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457790 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_3, prime_t23_5, prime_t23_307, prime_t23_661, prime_t23_1759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457791 : Nat.totient 10708457791 = 10708457790 := by
  rw [← show ((([(10708457791, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457791 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_10708457791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457792 : Nat.totient 10708457792 = 5353101696 := by
  rw [← show ((([(2, 6), (5659, 1), (29567, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457792 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_5659, prime_t23_29567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457793 : Nat.totient 10708457793 = 6488280000 := by
  rw [← show ((([(3, 1), (11, 1), (4021, 1), (80701, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457793 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_3, prime_t23_11, prime_t23_4021, prime_t23_80701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457794 : Nat.totient 10708457794 = 5039274240 := by
  rw [← show ((([(2, 1), (17, 1), (314954641, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457794 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_2, prime_t23_17, prime_lucas_314954641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t23_10708457795 : Nat.totient 10708457795 = 7342942320 := by
  rw [← show ((([(5, 1), (7, 2), (43707991, 1)] : List FactorBlock).map factorBlockValue).prod) = 10708457795 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t23_5, prime_t23_7, prime_lucas_43707991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The fourteenth finite diagonal certificate -/

theorem certifiedKill_diagonal_t23 :
    certifiedKill (periodLcm 23) (periodLcm 23) 35 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t23_5354228881, phi_t23_5354228882, phi_t23_5354228883, phi_t23_5354228884, phi_t23_5354228885, phi_t23_5354228886, phi_t23_5354228887, phi_t23_5354228888, phi_t23_5354228889, phi_t23_5354228890, phi_t23_5354228891, phi_t23_5354228892, phi_t23_5354228893, phi_t23_5354228894, phi_t23_5354228895, phi_t23_5354228896, phi_t23_5354228897, phi_t23_5354228898, phi_t23_5354228899, phi_t23_5354228900, phi_t23_5354228901, phi_t23_5354228902, phi_t23_5354228903, phi_t23_5354228904, phi_t23_5354228905, phi_t23_5354228906, phi_t23_5354228907, phi_t23_5354228908, phi_t23_5354228909, phi_t23_5354228910, phi_t23_5354228911, phi_t23_5354228912, phi_t23_5354228913, phi_t23_5354228914, phi_t23_5354228915, phi_t23_10708457761, phi_t23_10708457762, phi_t23_10708457763, phi_t23_10708457764, phi_t23_10708457765, phi_t23_10708457766, phi_t23_10708457767, phi_t23_10708457768, phi_t23_10708457769, phi_t23_10708457770, phi_t23_10708457771, phi_t23_10708457772, phi_t23_10708457773, phi_t23_10708457774, phi_t23_10708457775, phi_t23_10708457776, phi_t23_10708457777, phi_t23_10708457778, phi_t23_10708457779, phi_t23_10708457780, phi_t23_10708457781, phi_t23_10708457782, phi_t23_10708457783, phi_t23_10708457784, phi_t23_10708457785, phi_t23_10708457786, phi_t23_10708457787, phi_t23_10708457788, phi_t23_10708457789, phi_t23_10708457790, phi_t23_10708457791, phi_t23_10708457792, phi_t23_10708457793, phi_t23_10708457794, phi_t23_10708457795]

/-- The thirteen-scale prefix through t=19 plus the t=23 extension all fire. -/
theorem certifiedKill_diagonal_all_imported_through_t23 :
    ((∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t)) ∧
      certifiedKill (periodLcm 19) (periodLcm 19) 32) ∧
      certifiedKill (periodLcm 23) (periodLcm 23) 35 :=
  ⟨certifiedKill_diagonal_all_imported_through_t19, certifiedKill_diagonal_t23⟩

#print axioms certifiedKill_diagonal_all_imported_through_t23

end TotientTailPeriodKiller
end Erdos249257
