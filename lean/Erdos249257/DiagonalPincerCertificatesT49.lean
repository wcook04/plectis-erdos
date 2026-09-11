import Erdos249257.DiagonalPincerCertificatesT47
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64

/-!
# The t=49 diagonal-pincer certificate

This generated extension consumes 121 new large-prime Lucas roots
and 1121 recursive Pratt dependencies, reuses 0 earlier certificates,
reconstructs all 152 Euler totients in the t=49 window, and proves the
twenty-fourth finite diagonal kill without `native_decide`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=49 window -/

private theorem prime_t49_2 : Nat.Prime 2 := by norm_num
private theorem prime_t49_3 : Nat.Prime 3 := by norm_num
private theorem prime_t49_5 : Nat.Prime 5 := by norm_num
private theorem prime_t49_7 : Nat.Prime 7 := by norm_num
private theorem prime_t49_11 : Nat.Prime 11 := by norm_num
private theorem prime_t49_13 : Nat.Prime 13 := by norm_num
private theorem prime_t49_17 : Nat.Prime 17 := by norm_num
private theorem prime_t49_19 : Nat.Prime 19 := by norm_num
private theorem prime_t49_23 : Nat.Prime 23 := by norm_num
private theorem prime_t49_29 : Nat.Prime 29 := by norm_num
private theorem prime_t49_31 : Nat.Prime 31 := by norm_num
private theorem prime_t49_37 : Nat.Prime 37 := by norm_num
private theorem prime_t49_41 : Nat.Prime 41 := by norm_num
private theorem prime_t49_43 : Nat.Prime 43 := by norm_num
private theorem prime_t49_47 : Nat.Prime 47 := by norm_num
private theorem prime_t49_53 : Nat.Prime 53 := by norm_num
private theorem prime_t49_59 : Nat.Prime 59 := by norm_num
private theorem prime_t49_61 : Nat.Prime 61 := by norm_num
private theorem prime_t49_67 : Nat.Prime 67 := by norm_num
private theorem prime_t49_71 : Nat.Prime 71 := by norm_num
private theorem prime_t49_73 : Nat.Prime 73 := by norm_num
private theorem prime_t49_79 : Nat.Prime 79 := by norm_num
private theorem prime_t49_83 : Nat.Prime 83 := by norm_num
private theorem prime_t49_89 : Nat.Prime 89 := by norm_num
private theorem prime_t49_97 : Nat.Prime 97 := by norm_num
private theorem prime_t49_101 : Nat.Prime 101 := by norm_num
private theorem prime_t49_103 : Nat.Prime 103 := by norm_num
private theorem prime_t49_109 : Nat.Prime 109 := by norm_num
private theorem prime_t49_113 : Nat.Prime 113 := by norm_num
private theorem prime_t49_131 : Nat.Prime 131 := by norm_num
private theorem prime_t49_137 : Nat.Prime 137 := by norm_num
private theorem prime_t49_139 : Nat.Prime 139 := by norm_num
private theorem prime_t49_151 : Nat.Prime 151 := by norm_num
private theorem prime_t49_157 : Nat.Prime 157 := by norm_num
private theorem prime_t49_167 : Nat.Prime 167 := by norm_num
private theorem prime_t49_179 : Nat.Prime 179 := by norm_num
private theorem prime_t49_191 : Nat.Prime 191 := by norm_num
private theorem prime_t49_199 : Nat.Prime 199 := by norm_num
private theorem prime_t49_211 : Nat.Prime 211 := by norm_num
private theorem prime_t49_229 : Nat.Prime 229 := by norm_num
private theorem prime_t49_239 : Nat.Prime 239 := by norm_num
private theorem prime_t49_241 : Nat.Prime 241 := by norm_num
private theorem prime_t49_269 : Nat.Prime 269 := by norm_num
private theorem prime_t49_277 : Nat.Prime 277 := by norm_num
private theorem prime_t49_281 : Nat.Prime 281 := by norm_num
private theorem prime_t49_293 : Nat.Prime 293 := by norm_num
private theorem prime_t49_311 : Nat.Prime 311 := by norm_num
private theorem prime_t49_349 : Nat.Prime 349 := by norm_num
private theorem prime_t49_373 : Nat.Prime 373 := by norm_num
private theorem prime_t49_383 : Nat.Prime 383 := by norm_num
private theorem prime_t49_397 : Nat.Prime 397 := by norm_num
private theorem prime_t49_421 : Nat.Prime 421 := by norm_num
private theorem prime_t49_431 : Nat.Prime 431 := by norm_num
private theorem prime_t49_499 : Nat.Prime 499 := by norm_num
private theorem prime_t49_563 : Nat.Prime 563 := by norm_num
private theorem prime_t49_593 : Nat.Prime 593 := by norm_num
private theorem prime_t49_617 : Nat.Prime 617 := by norm_num
private theorem prime_t49_647 : Nat.Prime 647 := by norm_num
private theorem prime_t49_739 : Nat.Prime 739 := by norm_num
private theorem prime_t49_773 : Nat.Prime 773 := by norm_num
private theorem prime_t49_797 : Nat.Prime 797 := by norm_num
private theorem prime_t49_859 : Nat.Prime 859 := by norm_num
private theorem prime_t49_877 : Nat.Prime 877 := by norm_num
private theorem prime_t49_941 : Nat.Prime 941 := by norm_num
private theorem prime_t49_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_t49_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_t49_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_t49_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_t49_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_t49_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_t49_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_t49_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_t49_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_t49_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_t49_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_t49_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_t49_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_t49_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_t49_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_t49_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_t49_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_t49_2609 : Nat.Prime 2609 := by norm_num
private theorem prime_t49_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_t49_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_t49_3221 : Nat.Prime 3221 := by norm_num
private theorem prime_t49_3257 : Nat.Prime 3257 := by norm_num
private theorem prime_t49_3323 : Nat.Prime 3323 := by norm_num
private theorem prime_t49_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_t49_3851 : Nat.Prime 3851 := by norm_num
private theorem prime_t49_5483 : Nat.Prime 5483 := by norm_num
private theorem prime_t49_6323 : Nat.Prime 6323 := by norm_num
private theorem prime_t49_6823 : Nat.Prime 6823 := by norm_num
private theorem prime_t49_8819 : Nat.Prime 8819 := by norm_num
private theorem prime_t49_11117 : Nat.Prime 11117 := by norm_num
private theorem prime_t49_12503 : Nat.Prime 12503 := by norm_num
private theorem prime_t49_13879 : Nat.Prime 13879 := by norm_num
private theorem prime_t49_14107 : Nat.Prime 14107 := by norm_num
private theorem prime_t49_14173 : Nat.Prime 14173 := by norm_num
private theorem prime_t49_14537 : Nat.Prime 14537 := by norm_num
private theorem prime_t49_14867 : Nat.Prime 14867 := by norm_num
private theorem prime_t49_15199 : Nat.Prime 15199 := by norm_num
private theorem prime_t49_16087 : Nat.Prime 16087 := by norm_num
private theorem prime_t49_16189 : Nat.Prime 16189 := by norm_num
private theorem prime_t49_17137 : Nat.Prime 17137 := by norm_num
private theorem prime_t49_19541 : Nat.Prime 19541 := by norm_num
private theorem prime_t49_21727 : Nat.Prime 21727 := by norm_num
private theorem prime_t49_25031 : Nat.Prime 25031 := by norm_num
private theorem prime_t49_28031 : Nat.Prime 28031 := by norm_num
private theorem prime_t49_30517 : Nat.Prime 30517 := by norm_num
private theorem prime_t49_31223 : Nat.Prime 31223 := by norm_num
private theorem prime_t49_33023 : Nat.Prime 33023 := by norm_num
private theorem prime_t49_36973 : Nat.Prime 36973 := by norm_num
private theorem prime_t49_39047 : Nat.Prime 39047 := by norm_num
private theorem prime_t49_40559 : Nat.Prime 40559 := by norm_num
private theorem prime_t49_43759 : Nat.Prime 43759 := by norm_num
private theorem prime_t49_52627 : Nat.Prime 52627 := by norm_num
private theorem prime_t49_54001 : Nat.Prime 54001 := by norm_num
private theorem prime_t49_83227 : Nat.Prime 83227 := by norm_num
private theorem prime_t49_84811 : Nat.Prime 84811 := by norm_num
private theorem prime_t49_87407 : Nat.Prime 87407 := by norm_num
private theorem prime_t49_89113 : Nat.Prime 89113 := by norm_num
private theorem prime_t49_94793 : Nat.Prime 94793 := by norm_num
private theorem prime_t49_151883 : Nat.Prime 151883 := by norm_num
private theorem prime_t49_170711 : Nat.Prime 170711 := by norm_num
private theorem prime_t49_192637 : Nat.Prime 192637 := by norm_num
private theorem prime_t49_204857 : Nat.Prime 204857 := by norm_num
private theorem prime_t49_218527 : Nat.Prime 218527 := by norm_num
private theorem prime_t49_228457 : Nat.Prime 228457 := by norm_num
private theorem prime_t49_267739 : Nat.Prime 267739 := by norm_num
private theorem prime_t49_277961 : Nat.Prime 277961 := by norm_num
private theorem prime_t49_305297 : Nat.Prime 305297 := by norm_num
private theorem prime_t49_313561 : Nat.Prime 313561 := by norm_num
private theorem prime_t49_314491 : Nat.Prime 314491 := by norm_num
private theorem prime_t49_372263 : Nat.Prime 372263 := by norm_num
private theorem prime_t49_437401 : Nat.Prime 437401 := by norm_num
private theorem prime_t49_439289 : Nat.Prime 439289 := by norm_num
private theorem prime_t49_550903 : Nat.Prime 550903 := by norm_num
private theorem prime_t49_619561 : Nat.Prime 619561 := by norm_num
private theorem prime_t49_638459 : Nat.Prime 638459 := by norm_num
private theorem prime_t49_702269 : Nat.Prime 702269 := by norm_num
private theorem prime_t49_746413 : Nat.Prime 746413 := by norm_num
private theorem prime_t49_783121 : Nat.Prime 783121 := by norm_num
private theorem prime_t49_1177237 : Nat.Prime 1177237 := by norm_num
private theorem prime_t49_1278881 : Nat.Prime 1278881 := by norm_num
private theorem prime_t49_1379423 : Nat.Prime 1379423 := by norm_num
private theorem prime_t49_1640621 : Nat.Prime 1640621 := by norm_num
private theorem prime_t49_1678757 : Nat.Prime 1678757 := by norm_num
private theorem prime_t49_1824047 : Nat.Prime 1824047 := by norm_num
private theorem prime_t49_1827869 : Nat.Prime 1827869 := by norm_num
private theorem prime_t49_3034523 : Nat.Prime 3034523 := by norm_num
private theorem prime_t49_3336649 : Nat.Prime 3336649 := by norm_num
private theorem prime_t49_3393779 : Nat.Prime 3393779 := by norm_num
private theorem prime_t49_4844171 : Nat.Prime 4844171 := by norm_num
private theorem prime_t49_5431861 : Nat.Prime 5431861 := by norm_num
private theorem prime_t49_5769703 : Nat.Prime 5769703 := by norm_num
private theorem prime_t49_7817479 : Nat.Prime 7817479 := by norm_num
private theorem prime_t49_8232971 : Nat.Prime 8232971 := by norm_num
private theorem prime_t49_8249599 : Nat.Prime 8249599 := by norm_num
private theorem prime_t49_10298333 : Nat.Prime 10298333 := by norm_num
private theorem prime_t49_11968207 : Nat.Prime 11968207 := by norm_num
private theorem prime_t49_17033447 : Nat.Prime 17033447 := by norm_num
private theorem prime_t49_20788913 : Nat.Prime 20788913 := by norm_num
private theorem prime_t49_28720127 : Nat.Prime 28720127 := by norm_num

/-! ## Exact t=49 window totients -/

private theorem phi_t49_3099044504245996706401 : Nat.totient 3099044504245996706401 = 3092732901161673235200 := by
  rw [← show ((([(593, 1), (2851, 1), (8249599, 1), (222199493, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_593, prime_t49_2851, prime_t49_8249599, prime_lucas_222199493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706402 : Nat.totient 3099044504245996706402 = 1549522249122059249152 := by
  rw [← show ((([(2, 1), (516434657, 1), (3000422669393, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_lucas_516434657, prime_lucas_3000422669393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706403 : Nat.totient 3099044504245996706403 = 2060719718328955347840 := by
  rw [← show ((([(3, 1), (397, 1), (19541, 1), (7817479, 1), (17033447, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_397, prime_t49_19541, prime_t49_7817479, prime_t49_17033447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706404 : Nat.totient 3099044504245996706404 = 1532731890939619945344 := by
  rw [← show ((([(2, 2), (113, 1), (499, 1), (13740066434843123, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_113, prime_t49_499, prime_lucas_13740066434843123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706405 : Nat.totient 3099044504245996706405 = 2478591797020141756800 := by
  rw [← show ((([(5, 1), (3851, 1), (184154683, 1), (873980057, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_t49_3851, prime_lucas_184154683, prime_lucas_873980057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706406 : Nat.totient 3099044504245996706406 = 1033014085874071949384 := by
  rw [← show ((([(2, 1), (3, 1), (1379423, 1), (374437295430287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_1379423, prime_lucas_374437295430287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706407 : Nat.totient 3099044504245996706407 = 2656323860782282891200 := by
  rw [← show ((([(7, 1), (442720643463713815201, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_7, prime_lucas_442720643463713815201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706408 : Nat.totient 3099044504245996706408 = 1549521966857530377600 := by
  rw [← show ((([(2, 3), (5431861, 1), (71316361562041, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5431861, prime_lucas_71316361562041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706409 : Nat.totient 3099044504245996706409 = 2041137745768447629432 := by
  rw [← show ((([(3, 2), (83, 1), (4148653954813917947, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_83, prime_lucas_4148653954813917947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706410 : Nat.totient 3099044504245996706410 = 1239610540199129069200 := by
  rw [← show ((([(2, 1), (5, 1), (170711, 1), (1815374817232631, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_170711, prime_lucas_1815374817232631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706411 : Nat.totient 3099044504245996706411 = 2816886520814416617600 := by
  rw [← show ((([(11, 2), (6823, 1), (204857, 1), (18323830381, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_11, prime_t49_6823, prime_t49_204857, prime_lucas_18323830381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706412 : Nat.totient 3099044504245996706412 = 1028692578386548088832 := by
  rw [← show ((([(2, 2), (3, 1), (239, 1), (55584257, 1), (19440026887, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_239, prime_lucas_55584257, prime_lucas_19440026887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706413 : Nat.totient 3099044504245996706413 = 2858213877356497265280 := by
  rw [← show ((([(13, 1), (1279, 1), (13879, 1), (13429373123161, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_13, prime_t49_1279, prime_t49_13879, prime_lucas_13429373123161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706414 : Nat.totient 3099044504245996706414 = 1328161930391141445600 := by
  rw [← show ((([(2, 1), (7, 1), (221360321731856907601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_7, prime_lucas_221360321731856907601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706415 : Nat.totient 3099044504245996706415 = 1651738332972196039296 := by
  rw [← show ((([(3, 1), (5, 1), (1523, 1), (10298333, 1), (13172545879, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_5, prime_t49_1523, prime_t49_10298333, prime_lucas_13172545879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706416 : Nat.totient 3099044504245996706416 = 1549522252122998353200 := by
  rw [← show ((([(2, 4), (193690281515374794151, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_lucas_193690281515374794151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706417 : Nat.totient 3099044504245996706417 = 2916747768702114547200 := by
  rw [← show ((([(17, 1), (182296735543882159201, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_17, prime_lucas_182296735543882159201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706418 : Nat.totient 3099044504245996706418 = 1029692940227738598240 := by
  rw [← show ((([(2, 1), (3, 2), (311, 1), (3393779, 1), (163121558029, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_311, prime_t49_3393779, prime_lucas_163121558029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706419 : Nat.totient 3099044504245996706419 = 2935903952534921030016 := by
  rw [← show ((([(19, 1), (89113, 1), (1830345802370377, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_19, prime_t49_89113, prime_lucas_1830345802370377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706420 : Nat.totient 3099044504245996706420 = 1239142670306410007552 := by
  rw [← show ((([(2, 2), (5, 1), (2609, 1), (59391423998581769, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_2609, prime_lucas_59391423998581769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706421 : Nat.totient 3099044504245996706421 = 1770882573854855260800 := by
  rw [← show ((([(3, 1), (7, 1), (147573547821237938401, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_7, prime_lucas_147573547821237938401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706422 : Nat.totient 3099044504245996706422 = 1407189393498961459200 := by
  rw [← show ((([(2, 1), (11, 1), (1361, 1), (3257, 1), (31778196666313, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_11, prime_t49_1361, prime_t49_3257, prime_lucas_31778196666313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706423 : Nat.totient 3099044504245996706423 = 2964119171830952174424 := by
  rw [← show ((([(23, 1), (16087, 1), (8375773320196423, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_23, prime_t49_16087, prime_lucas_8375773320196423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706424 : Nat.totient 3099044504245996706424 = 998396765096429212800 := by
  rw [← show ((([(2, 3), (3, 1), (53, 1), (67, 1), (36363518542265051, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_53, prime_t49_67, prime_lucas_36363518542265051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706425 : Nat.totient 3099044504245996706425 = 2479235603396797365120 := by
  rw [← show ((([(5, 2), (123961780169839868257, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_lucas_123961780169839868257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706426 : Nat.totient 3099044504245996706426 = 1430309830712345833536 := by
  rw [← show ((([(2, 1), (13, 1), (83227, 1), (1177237, 1), (1216539799, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_13, prime_t49_83227, prime_t49_1177237, prime_lucas_1216539799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706427 : Nat.totient 3099044504245996706427 = 2066029669497331137564 := by
  rw [← show ((([(3, 4), (38259808694395021067, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_lucas_38259808694395021067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706428 : Nat.totient 3099044504245996706428 = 1327265119587846798720 := by
  rw [← show ((([(2, 2), (7, 1), (1481, 1), (210808223, 1), (354508927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_7, prime_t49_1481, prime_lucas_210808223, prime_lucas_354508927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706429 : Nat.totient 3099044504245996706429 = 2969337503242638528000 := by
  rw [← show ((([(29, 1), (131, 1), (1278881, 1), (637864429291, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_29, prime_t49_131, prime_t49_1278881, prime_lucas_637864429291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706430 : Nat.totient 3099044504245996706430 = 826411858883435618816 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (92701577, 1), (1114344402953, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_5, prime_lucas_92701577, prime_lucas_1114344402953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706431 : Nat.totient 3099044504245996706431 = 2999075314799495516160 := by
  rw [← show ((([(31, 1), (252392033, 1), (396086898497, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_31, prime_lucas_252392033, prime_lucas_396086898497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706432 : Nat.totient 3099044504245996706432 = 1549518089683376386816 := by
  rw [← show ((([(2, 7), (372263, 1), (65038118720963, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_372263, prime_lucas_65038118720963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706433 : Nat.totient 3099044504245996706433 = 1846353619278919248960 := by
  rw [← show ((([(3, 1), (11, 1), (59, 1), (87407, 1), (18210239051677, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_11, prime_t49_59, prime_t49_87407, prime_lucas_18210239051677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706434 : Nat.totient 3099044504245996706434 = 1458373086496321617664 := by
  rw [← show ((([(2, 1), (17, 1), (1827869, 1), (49865919150629, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_17, prime_t49_1827869, prime_lucas_49865919150629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706435 : Nat.totient 3099044504245996706435 = 2125059088625826312960 := by
  rw [← show ((([(5, 1), (7, 1), (88544128692742763041, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_t49_7, prime_lucas_88544128692742763041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706436 : Nat.totient 3099044504245996706436 = 1032986895040371271104 := by
  rw [← show ((([(2, 2), (3, 2), (36973, 1), (2328309024487837, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_36973, prime_lucas_2328309024487837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706437 : Nat.totient 3099044504245996706437 = 3015286544671780579200 := by
  rw [← show ((([(37, 1), (83757959574216127201, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_37, prime_lucas_83757959574216127201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706438 : Nat.totient 3099044504245996706438 = 1464032877129334969056 := by
  rw [← show ((([(2, 1), (19, 1), (373, 1), (218642902797093037, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_19, prime_t49_373, prime_lucas_218642902797093037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706439 : Nat.totient 3099044504245996706439 = 1905073276514739840000 := by
  rw [← show ((([(3, 1), (13, 1), (941, 1), (437401, 1), (193060670861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_13, prime_t49_941, prime_t49_437401, prime_lucas_193060670861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706440 : Nat.totient 3099044504245996706440 = 1209674712168864737280 := by
  rw [← show ((([(2, 3), (5, 1), (73, 1), (103, 1), (1109, 1), (9291293748791, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_73, prime_t49_103, prime_t49_1109, prime_lucas_9291293748791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706441 : Nat.totient 3099044504245996706441 = 3023458052922923616000 := by
  rw [← show ((([(41, 1), (75586451323073090401, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_41, prime_lucas_75586451323073090401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706442 : Nat.totient 3099044504245996706442 = 885057813004981770048 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (2309, 1), (31956160203819389, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_7, prime_t49_2309, prime_lucas_31956160203819389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706443 : Nat.totient 3099044504245996706443 = 3026070903553724869920 := by
  rw [← show ((([(43, 1), (3389, 1), (314491, 1), (67620685199, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_43, prime_t49_3389, prime_t49_314491, prime_lucas_67620685199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706444 : Nat.totient 3099044504245996706444 = 1408649280346714731840 := by
  rw [← show ((([(2, 2), (11, 1), (192637, 1), (365624618541373, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_11, prime_t49_192637, prime_lucas_365624618541373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706445 : Nat.totient 3099044504245996706445 = 1652823735597864910080 := by
  rw [← show ((([(3, 2), (5, 1), (68867655649911037921, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_5, prime_lucas_68867655649911037921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706446 : Nat.totient 3099044504245996706446 = 1481053091238127974336 := by
  rw [← show ((([(2, 1), (23, 1), (1487, 1), (14537, 1), (3116622648679, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_23, prime_t49_1487, prime_t49_14537, prime_lucas_3116622648679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706447 : Nat.totient 3099044504245996706447 = 3033107387134379755200 := by
  rw [← show ((([(47, 1), (65937117111616951201, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_47, prime_lucas_65937117111616951201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706448 : Nat.totient 3099044504245996706448 = 1032932213391011312512 := by
  rw [← show ((([(2, 4), (3, 1), (12503, 1), (5163834853378517, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_12503, prime_lucas_5163834853378517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706449 : Nat.totient 3099044504245996706449 = 2656075362541739792640 := by
  rw [← show ((([(7, 2), (11117, 1), (277961, 1), (20467286173, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_7, prime_t49_11117, prime_t49_277961, prime_lucas_20467286173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706450 : Nat.totient 3099044504245996706450 = 1239617801698398682560 := by
  rw [← show ((([(2, 1), (5, 2), (61980890084919934129, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_lucas_61980890084919934129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706451 : Nat.totient 3099044504245996706451 = 1944498512468076364288 := by
  rw [← show ((([(3, 1), (17, 2), (3574445794978081553, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_17, prime_lucas_3574445794978081553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706452 : Nat.totient 3099044504245996706452 = 1427356822481877811200 := by
  rw [← show ((([(2, 2), (13, 1), (647, 1), (1889, 1), (305297, 1), (159722351, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_13, prime_t49_647, prime_t49_1889, prime_t49_305297, prime_lucas_159722351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706453 : Nat.totient 3099044504245996706453 = 3099044127827256493740 := by
  rw [← show ((([(8232971, 1), (376418731979743, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_8232971, prime_lucas_376418731979743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706454 : Nat.totient 3099044504245996706454 = 1033014834748665568800 := by
  rw [← show ((([(2, 1), (3, 3), (57389713041592531601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_lucas_57389713041592531601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706455 : Nat.totient 3099044504245996706455 = 2253843360625192128000 := by
  rw [← show ((([(5, 1), (11, 1), (313561, 1), (179697933459721, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_t49_11, prime_t49_313561, prime_lucas_179697933459721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706456 : Nat.totient 3099044504245996706456 = 1325802042453325484160 := by
  rw [← show ((([(2, 3), (7, 1), (563, 1), (1640621, 1), (59913283987, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_7, prime_t49_563, prime_t49_1640621, prime_lucas_59913283987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706457 : Nat.totient 3099044504245996706457 = 1918943203427580617280 := by
  rw [← show ((([(3, 1), (19, 1), (71, 1), (179, 1), (4278007854974989, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_19, prime_t49_71, prime_t49_179, prime_lucas_4278007854974989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706458 : Nat.totient 3099044504245996706458 = 1496090448492481385712 := by
  rw [← show ((([(2, 1), (29, 1), (826556239, 1), (64643879359, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_29, prime_lucas_826556239, prime_lucas_64643879359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706459 : Nat.totient 3099044504245996706459 = 3099044504245996706458 := by
  rw [← show ((([(3099044504245996706459, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_3099044504245996706459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706460 : Nat.totient 3099044504245996706460 = 804783819764016000000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (61, 1), (101, 1), (25031, 1), (334924681951, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_5, prime_t49_61, prime_t49_101, prime_t49_25031, prime_lucas_334924681951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706461 : Nat.totient 3099044504245996706461 = 3076749220042788096924 := by
  rw [← show ((([(139, 1), (22295284203208609399, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_139, prime_lucas_22295284203208609399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706462 : Nat.totient 3099044504245996706462 = 1482641438479913194560 := by
  rw [← show ((([(2, 1), (31, 1), (89, 1), (31223, 1), (17987528200783, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_31, prime_t49_89, prime_t49_31223, prime_lucas_17987528200783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706463 : Nat.totient 3099044504245996706463 = 1760013655738951219200 := by
  rw [← show ((([(3, 2), (7, 1), (277, 1), (877, 1), (1321, 1), (1559, 1), (98323871, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_7, prime_t49_277, prime_t49_877, prime_t49_1321, prime_t49_1559, prime_lucas_98323871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706464 : Nat.totient 3099044504245996706464 = 1547577210127814048512 := by
  rw [← show ((([(2, 5), (797, 1), (1824047, 1), (66616757303, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_797, prime_t49_1824047, prime_lucas_66616757303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706465 : Nat.totient 3099044504245996706465 = 2252408637454978489344 := by
  rw [← show ((([(5, 1), (13, 1), (109, 1), (157, 1), (3323, 1), (838412924939, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_t49_13, prime_t49_109, prime_t49_157, prime_t49_3323, prime_lucas_838412924939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706466 : Nat.totient 3099044504245996706466 = 937142333146977914880 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (617, 1), (2137, 1), (746413, 1), (47710613, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_11, prime_t49_617, prime_t49_2137, prime_t49_746413, prime_lucas_47710613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706467 : Nat.totient 3099044504245996706467 = 3099038878855493206776 := by
  rw [← show ((([(550903, 1), (5625390502948789, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_550903, prime_lucas_5625390502948789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706468 : Nat.totient 3099044504245996706468 = 1458373881509601583104 := by
  rw [← show ((([(2, 2), (17, 1), (516250297, 1), (88279240033, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_17, prime_lucas_516250297, prime_lucas_88279240033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706469 : Nat.totient 3099044504245996706469 = 1976202291564108647600 := by
  rw [← show ((([(3, 1), (23, 1), (2190487991, 1), (20503964711, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_23, prime_lucas_2190487991, prime_lucas_20503964711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706470 : Nat.totient 3099044504245996706470 = 1062335758147617946848 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (5483, 1), (8074423553961587, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_7, prime_t49_5483, prime_lucas_8074423553961587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706471 : Nat.totient 3099044504245996706471 = 3050707968550015488000 := by
  rw [← show ((([(151, 1), (199, 1), (349, 1), (859, 1), (439289, 1), (783121, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_151, prime_t49_199, prime_t49_349, prime_t49_859, prime_t49_439289, prime_t49_783121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706472 : Nat.totient 3099044504245996706472 = 1032989365313157096096 := by
  rw [← show ((([(2, 3), (3, 2), (40559, 1), (1061226479479139, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_40559, prime_lucas_1061226479479139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706473 : Nat.totient 3099044504245996706473 = 3099044502982918411600 := by
  rw [← show ((([(2458349573, 1), (1260619945301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_2458349573, prime_lucas_1260619945301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706474 : Nat.totient 3099044504245996706474 = 1491608063636940130560 := by
  rw [← show ((([(2, 1), (37, 1), (167, 1), (229, 1), (3221, 1), (339980035567, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_37, prime_t49_167, prime_t49_229, prime_t49_3221, prime_lucas_339980035567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706475 : Nat.totient 3099044504245996706475 = 1651311545537848521600 := by
  rw [← show ((([(3, 1), (5, 2), (1093, 1), (37804751500408621, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_5, prime_t49_1093, prime_lucas_37804751500408621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_3099044504245996706476 : Nat.totient 3099044504245996706476 = 1447977081099389607936 := by
  rw [← show ((([(2, 2), (19, 1), (79, 1), (1097, 1), (21727, 1), (94793, 1), (228457, 1)] : List FactorBlock).map factorBlockValue).prod) = 3099044504245996706476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_19, prime_t49_79, prime_t49_1097, prime_t49_21727, prime_t49_94793, prime_t49_228457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412801 : Nat.totient 6198089008491993412801 = 6198089007953797963204 := by
  rw [← show ((([(11774005559, 1), (526421444039, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_11774005559, prime_lucas_526421444039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412802 : Nat.totient 6198089008491993412802 = 3092732901161673235200 := by
  rw [← show ((([(2, 1), (593, 1), (2851, 1), (8249599, 1), (222199493, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_593, prime_t49_2851, prime_t49_8249599, prime_lucas_222199493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412803 : Nat.totient 6198089008491993412803 = 4132059338994662275200 := by
  rw [← show ((([(3, 1), (2066029669497331137601, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_lucas_2066029669497331137601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412804 : Nat.totient 6198089008491993412804 = 3099044498244118498304 := by
  rw [← show ((([(2, 2), (516434657, 1), (3000422669393, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_lucas_516434657, prime_lucas_3000422669393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412805 : Nat.totient 6198089008491993412805 = 4958471206793594730240 := by
  rw [← show ((([(5, 1), (1239617801698398682561, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_lucas_1239617801698398682561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412806 : Nat.totient 6198089008491993412806 = 2060719718328955347840 := by
  rw [← show ((([(2, 1), (3, 1), (397, 1), (19541, 1), (7817479, 1), (17033447, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_397, prime_t49_19541, prime_t49_7817479, prime_t49_17033447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412807 : Nat.totient 6198089008491993412807 = 5149092032850766053888 := by
  rw [← show ((([(7, 1), (59, 1), (73, 1), (2617, 1), (78556327905779, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_7, prime_t49_59, prime_t49_73, prime_t49_2617, prime_lucas_78556327905779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412808 : Nat.totient 6198089008491993412808 = 3065463781879239890688 := by
  rw [← show ((([(2, 3), (113, 1), (499, 1), (13740066434843123, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_113, prime_t49_499, prime_lucas_13740066434843123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412809 : Nat.totient 6198089008491993412809 = 4131667222819599022560 := by
  rw [← show ((([(3, 2), (14867, 1), (43759, 1), (218527, 1), (4844171, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_14867, prime_t49_43759, prime_t49_218527, prime_t49_4844171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412810 : Nat.totient 6198089008491993412810 = 2478591797020141756800 := by
  rw [← show ((([(2, 1), (5, 1), (3851, 1), (184154683, 1), (873980057, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_3851, prime_lucas_184154683, prime_lucas_873980057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412811 : Nat.totient 6198089008491993412811 = 5633980427773082880000 := by
  rw [← show ((([(11, 1), (15199, 1), (33023, 1), (54001, 1), (20788913, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_11, prime_t49_15199, prime_t49_33023, prime_t49_54001, prime_t49_20788913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412812 : Nat.totient 6198089008491993412812 = 2066028171748143898768 := by
  rw [← show ((([(2, 2), (3, 1), (1379423, 1), (374437295430287, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_1379423, prime_lucas_374437295430287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412813 : Nat.totient 6198089008491993412813 = 5716517195013828973824 := by
  rw [← show ((([(13, 1), (1193, 1), (399644658488103257, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_13, prime_t49_1193, prime_lucas_399644658488103257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412814 : Nat.totient 6198089008491993412814 = 2656323860782282891200 := by
  rw [← show ((([(2, 1), (7, 1), (442720643463713815201, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_7, prime_lucas_442720643463713815201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412815 : Nat.totient 6198089008491993412815 = 3305584658429065980576 := by
  rw [← show ((([(3, 1), (5, 1), (52627, 1), (7851595832927323, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_5, prime_t49_52627, prime_lucas_7851595832927323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412816 : Nat.totient 6198089008491993412816 = 3099043933715060755200 := by
  rw [← show ((([(2, 4), (5431861, 1), (71316361562041, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5431861, prime_lucas_71316361562041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412817 : Nat.totient 6198089008491993412817 = 5811809680387856491264 := by
  rw [← show ((([(17, 1), (269, 1), (1355366063523287429, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_17, prime_t49_269, prime_lucas_1355366063523287429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412818 : Nat.totient 6198089008491993412818 = 2041137745768447629432 := by
  rw [← show ((([(2, 1), (3, 2), (83, 1), (4148653954813917947, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_83, prime_lucas_4148653954813917947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412819 : Nat.totient 6198089008491993412819 = 5813736230707912101600 := by
  rw [← show ((([(19, 1), (101, 1), (28720127, 1), (112459585363, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_19, prime_t49_101, prime_t49_28720127, prime_lucas_112459585363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412820 : Nat.totient 6198089008491993412820 = 2479221080398258138400 := by
  rw [← show ((([(2, 2), (5, 1), (170711, 1), (1815374817232631, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_170711, prime_lucas_1815374817232631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412821 : Nat.totient 6198089008491993412821 = 3509271889473841616448 := by
  rw [← show ((([(3, 1), (7, 1), (109, 1), (2707771519655741989, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_7, prime_t49_109, prime_lucas_2707771519655741989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412822 : Nat.totient 6198089008491993412822 = 2816886520814416617600 := by
  rw [← show ((([(2, 1), (11, 2), (6823, 1), (204857, 1), (18323830381, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_11, prime_t49_6823, prime_t49_204857, prime_lucas_18323830381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412823 : Nat.totient 6198089008491993412823 = 5925948190413756400896 := by
  rw [← show ((([(23, 1), (2237, 1), (702269, 1), (171538058617, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_23, prime_t49_2237, prime_t49_702269, prime_lucas_171538058617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412824 : Nat.totient 6198089008491993412824 = 2057385156773096177664 := by
  rw [← show ((([(2, 3), (3, 1), (239, 1), (55584257, 1), (19440026887, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_239, prime_lucas_55584257, prime_lucas_19440026887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412825 : Nat.totient 6198089008491993412825 = 4958471206793594730240 := by
  rw [← show ((([(5, 2), (247923560339679736513, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_lucas_247923560339679736513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412826 : Nat.totient 6198089008491993412826 = 2858213877356497265280 := by
  rw [← show ((([(2, 1), (13, 1), (1279, 1), (13879, 1), (13429373123161, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_13, prime_t49_1279, prime_t49_13879, prime_lucas_13429373123161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412827 : Nat.totient 6198089008491993412827 = 4132059338994662275200 := by
  rw [← show ((([(3, 3), (229558852166370126401, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_lucas_229558852166370126401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412828 : Nat.totient 6198089008491993412828 = 2656323860782282891200 := by
  rw [← show ((([(2, 2), (7, 1), (221360321731856907601, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_7, prime_lucas_221360321731856907601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412829 : Nat.totient 6198089008491993412829 = 5975840244576500653824 := by
  rw [← show ((([(29, 1), (739, 1), (14107, 1), (20501267203537, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_29, prime_t49_739, prime_t49_14107, prime_lucas_20501267203537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412830 : Nat.totient 6198089008491993412830 = 1651738332972196039296 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1523, 1), (10298333, 1), (13172545879, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_5, prime_t49_1523, prime_t49_10298333, prime_lucas_13172545879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412831 : Nat.totient 6198089008491993412831 = 5983880914887351386400 := by
  rw [← show ((([(31, 1), (421, 1), (267739, 1), (1773790734679, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_31, prime_t49_421, prime_t49_267739, prime_lucas_1773790734679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412832 : Nat.totient 6198089008491993412832 = 3099044504245996706400 := by
  rw [← show ((([(2, 5), (193690281515374794151, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_lucas_193690281515374794151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412833 : Nat.totient 6198089008491993412833 = 3738614653980521658000 := by
  rw [← show ((([(3, 1), (11, 1), (211, 1), (890146346185838491, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_11, prime_t49_211, prime_lucas_890146346185838491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412834 : Nat.totient 6198089008491993412834 = 2916747768702114547200 := by
  rw [← show ((([(2, 1), (17, 1), (182296735543882159201, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_17, prime_lucas_182296735543882159201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412835 : Nat.totient 6198089008491993412835 = 4202226334754962854912 := by
  rw [← show ((([(5, 1), (7, 1), (89, 1), (30517, 1), (65201549987237, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_t49_7, prime_t49_89, prime_t49_30517, prime_lucas_65201549987237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412836 : Nat.totient 6198089008491993412836 = 2059385880455477196480 := by
  rw [← show ((([(2, 2), (3, 2), (311, 1), (3393779, 1), (163121558029, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_311, prime_t49_3393779, prime_lucas_163121558029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412837 : Nat.totient 6198089008491993412837 = 6022762138451627992512 := by
  rw [← show ((([(37, 1), (773, 1), (638459, 1), (339424805143, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_37, prime_t49_773, prime_t49_638459, prime_lucas_339424805143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412838 : Nat.totient 6198089008491993412838 = 2935903952534921030016 := by
  rw [← show ((([(2, 1), (19, 1), (89113, 1), (1830345802370377, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_19, prime_t49_89113, prime_lucas_1830345802370377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412839 : Nat.totient 6198089008491993412839 = 3814208619652501632096 := by
  rw [← show ((([(3, 1), (13, 1), (4485729839, 1), (35429097359, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_13, prime_lucas_4485729839, prime_lucas_35429097359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412840 : Nat.totient 6198089008491993412840 = 2478285340612820015104 := by
  rw [← show ((([(2, 3), (5, 1), (2609, 1), (59391423998581769, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_2609, prime_lucas_59391423998581769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412841 : Nat.totient 6198089008491993412841 = 6017658180158667571200 := by
  rw [← show ((([(41, 1), (241, 1), (1459, 1), (151883, 1), (2830690913, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_41, prime_t49_241, prime_t49_1459, prime_t49_151883, prime_lucas_2830690913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412842 : Nat.totient 6198089008491993412842 = 1770882573854855260800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (147573547821237938401, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_7, prime_lucas_147573547821237938401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412843 : Nat.totient 6198089008491993412843 = 5937360894634456980000 := by
  rw [← show ((([(43, 1), (71, 1), (191, 1), (84811, 1), (125327233531, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_43, prime_t49_71, prime_t49_191, prime_t49_84811, prime_lucas_125327233531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412844 : Nat.totient 6198089008491993412844 = 2814378786997922918400 := by
  rw [← show ((([(2, 2), (11, 1), (1361, 1), (3257, 1), (31778196666313, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_11, prime_t49_1361, prime_t49_3257, prime_lucas_31778196666313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412845 : Nat.totient 6198089008491993412845 = 3293883601191474547200 := by
  rw [← show ((([(3, 2), (5, 1), (281, 1), (490161250177302761, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_5, prime_t49_281, prime_lucas_490161250177302761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412846 : Nat.totient 6198089008491993412846 = 2964119171830952174424 := by
  rw [← show ((([(2, 1), (23, 1), (16087, 1), (8375773320196423, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_23, prime_t49_16087, prime_lucas_8375773320196423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412847 : Nat.totient 6198089008491993412847 = 6066214774268759510400 := by
  rw [← show ((([(47, 1), (131874234223233902401, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_47, prime_lucas_131874234223233902401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412848 : Nat.totient 6198089008491993412848 = 1996793530192858425600 := by
  rw [← show ((([(2, 4), (3, 1), (53, 1), (67, 1), (36363518542265051, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_53, prime_t49_67, prime_lucas_36363518542265051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412849 : Nat.totient 6198089008491993412849 = 5312647277664336322272 := by
  rw [← show ((([(7, 3), (11968207, 1), (1509852757849, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_7, prime_t49_11968207, prime_lucas_1509852757849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412850 : Nat.totient 6198089008491993412850 = 2479235603396797365120 := by
  rw [← show ((([(2, 1), (5, 2), (123961780169839868257, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_lucas_123961780169839868257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412851 : Nat.totient 6198089008491993412851 = 3888895108460474789376 := by
  rw [← show ((([(3, 1), (17, 1), (39047, 1), (1678757, 1), (1854010219, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_17, prime_t49_39047, prime_t49_1678757, prime_lucas_1854010219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412852 : Nat.totient 6198089008491993412852 = 2860619661424691667072 := by
  rw [← show ((([(2, 2), (13, 1), (83227, 1), (1177237, 1), (1216539799, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_13, prime_t49_83227, prime_t49_1177237, prime_lucas_1216539799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412853 : Nat.totient 6198089008491993412853 = 6193817410278008577900 := by
  rw [← show ((([(1451, 1), (4271598213984833503, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_1451, prime_lucas_4271598213984833503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412854 : Nat.totient 6198089008491993412854 = 2066029669497331137564 := by
  rw [← show ((([(2, 1), (3, 4), (38259808694395021067, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_lucas_38259808694395021067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412855 : Nat.totient 6198089008491993412855 = 4507701097085086118400 := by
  rw [← show ((([(5, 1), (11, 1), (112692527427127152961, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_t49_11, prime_lucas_112692527427127152961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412856 : Nat.totient 6198089008491993412856 = 2654530239175693597440 := by
  rw [← show ((([(2, 3), (7, 1), (1481, 1), (210808223, 1), (354508927, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_7, prime_t49_1481, prime_lucas_210808223, prime_lucas_354508927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412857 : Nat.totient 6198089008491993412857 = 3860778094169244401664 := by
  rw [← show ((([(3, 1), (19, 1), (97, 1), (293, 1), (17137, 1), (223258910813, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_19, prime_t49_97, prime_t49_293, prime_t49_17137, prime_lucas_223258910813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412858 : Nat.totient 6198089008491993412858 = 2969337503242638528000 := by
  rw [← show ((([(2, 1), (29, 1), (131, 1), (1278881, 1), (637864429291, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_29, prime_t49_131, prime_t49_1278881, prime_lucas_637864429291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412859 : Nat.totient 6198089008491993412859 = 6095789702585036388000 := by
  rw [← show ((([(61, 1), (8819, 1), (11521489571681101, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_61, prime_t49_8819, prime_lucas_11521489571681101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412860 : Nat.totient 6198089008491993412860 = 1652823717766871237632 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (92701577, 1), (1114344402953, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_5, prime_lucas_92701577, prime_lucas_1114344402953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412861 : Nat.totient 6198089008491993412861 = 6152457487684707348480 := by
  rw [← show ((([(137, 1), (16189, 1), (619561, 1), (4510587857, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_137, prime_t49_16189, prime_t49_619561, prime_lucas_4510587857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412862 : Nat.totient 6198089008491993412862 = 2999075314799495516160 := by
  rw [← show ((([(2, 1), (31, 1), (252392033, 1), (396086898497, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_31, prime_lucas_252392033, prime_lucas_396086898497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412863 : Nat.totient 6198089008491993412863 = 3532268476359656523072 := by
  rw [← show ((([(3, 2), (7, 1), (383, 1), (14173, 1), (18124110366539, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_7, prime_t49_383, prime_t49_14173, prime_lucas_18124110366539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412864 : Nat.totient 6198089008491993412864 = 3099036179366752773632 := by
  rw [← show ((([(2, 8), (372263, 1), (65038118720963, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_372263, prime_lucas_65038118720963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412865 : Nat.totient 6198089008491993412865 = 4577048972981765747712 := by
  rw [← show ((([(5, 1), (13, 1), (3336649, 1), (28578137980729, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_5, prime_t49_13, prime_t49_3336649, prime_lucas_28578137980729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412866 : Nat.totient 6198089008491993412866 = 1846353619278919248960 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (59, 1), (87407, 1), (18210239051677, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_11, prime_t49_59, prime_t49_87407, prime_lucas_18210239051677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412867 : Nat.totient 6198089008491993412867 = 6183708291534935423080 := by
  rw [← show ((([(431, 1), (14380716957057989357, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_431, prime_lucas_14380716957057989357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412868 : Nat.totient 6198089008491993412868 = 2916746172992643235328 := by
  rw [← show ((([(2, 2), (17, 1), (1827869, 1), (49865919150629, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_17, prime_t49_1827869, prime_lucas_49865919150629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412869 : Nat.totient 6198089008491993412869 = 3952263583927185652400 := by
  rw [← show ((([(3, 1), (23, 1), (28031, 1), (3204572685051071, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_23, prime_t49_28031, prime_lucas_3204572685051071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412870 : Nat.totient 6198089008491993412870 = 2125059088625826312960 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (88544128692742763041, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_5, prime_t49_7, prime_lucas_88544128692742763041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412871 : Nat.totient 6198089008491993412871 = 6198086965967017428072 := by
  rw [← show ((([(3034523, 1), (2042524972950277, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3034523, prime_lucas_2042524972950277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412872 : Nat.totient 6198089008491993412872 = 2065973790080742542208 := by
  rw [← show ((([(2, 3), (3, 2), (36973, 1), (2328309024487837, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_3, prime_t49_36973, prime_lucas_2328309024487837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412873 : Nat.totient 6198089008491993412873 = 6119632185599689698708 := by
  rw [← show ((([(79, 1), (78456822892303714087, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_79, prime_lucas_78456822892303714087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412874 : Nat.totient 6198089008491993412874 = 3015286544671780579200 := by
  rw [← show ((([(2, 1), (37, 1), (83757959574216127201, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_37, prime_lucas_83757959574216127201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412875 : Nat.totient 6198089008491993412875 = 3305124093736468166400 := by
  rw [← show ((([(3, 1), (5, 3), (6323, 1), (5769703, 1), (453053929, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_3, prime_t49_5, prime_t49_6323, prime_t49_5769703, prime_lucas_453053929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t49_6198089008491993412876 : Nat.totient 6198089008491993412876 = 2928065754258669938112 := by
  rw [← show ((([(2, 2), (19, 1), (373, 1), (218642902797093037, 1)] : List FactorBlock).map factorBlockValue).prod) = 6198089008491993412876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t49_2, prime_t49_19, prime_t49_373, prime_lucas_218642902797093037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twenty-fourth finite diagonal certificate -/

theorem certifiedKill_diagonal_t49 :
    certifiedKill (periodLcm 49) (periodLcm 49) 76 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t49_3099044504245996706401, phi_t49_3099044504245996706402, phi_t49_3099044504245996706403, phi_t49_3099044504245996706404, phi_t49_3099044504245996706405, phi_t49_3099044504245996706406, phi_t49_3099044504245996706407, phi_t49_3099044504245996706408, phi_t49_3099044504245996706409, phi_t49_3099044504245996706410, phi_t49_3099044504245996706411, phi_t49_3099044504245996706412, phi_t49_3099044504245996706413, phi_t49_3099044504245996706414, phi_t49_3099044504245996706415, phi_t49_3099044504245996706416, phi_t49_3099044504245996706417, phi_t49_3099044504245996706418, phi_t49_3099044504245996706419, phi_t49_3099044504245996706420, phi_t49_3099044504245996706421, phi_t49_3099044504245996706422, phi_t49_3099044504245996706423, phi_t49_3099044504245996706424, phi_t49_3099044504245996706425, phi_t49_3099044504245996706426, phi_t49_3099044504245996706427, phi_t49_3099044504245996706428, phi_t49_3099044504245996706429, phi_t49_3099044504245996706430, phi_t49_3099044504245996706431, phi_t49_3099044504245996706432, phi_t49_3099044504245996706433, phi_t49_3099044504245996706434, phi_t49_3099044504245996706435, phi_t49_3099044504245996706436, phi_t49_3099044504245996706437, phi_t49_3099044504245996706438, phi_t49_3099044504245996706439, phi_t49_3099044504245996706440, phi_t49_3099044504245996706441, phi_t49_3099044504245996706442, phi_t49_3099044504245996706443, phi_t49_3099044504245996706444, phi_t49_3099044504245996706445, phi_t49_3099044504245996706446, phi_t49_3099044504245996706447, phi_t49_3099044504245996706448, phi_t49_3099044504245996706449, phi_t49_3099044504245996706450, phi_t49_3099044504245996706451, phi_t49_3099044504245996706452, phi_t49_3099044504245996706453, phi_t49_3099044504245996706454, phi_t49_3099044504245996706455, phi_t49_3099044504245996706456, phi_t49_3099044504245996706457, phi_t49_3099044504245996706458, phi_t49_3099044504245996706459, phi_t49_3099044504245996706460, phi_t49_3099044504245996706461, phi_t49_3099044504245996706462, phi_t49_3099044504245996706463, phi_t49_3099044504245996706464, phi_t49_3099044504245996706465, phi_t49_3099044504245996706466, phi_t49_3099044504245996706467, phi_t49_3099044504245996706468, phi_t49_3099044504245996706469, phi_t49_3099044504245996706470, phi_t49_3099044504245996706471, phi_t49_3099044504245996706472, phi_t49_3099044504245996706473, phi_t49_3099044504245996706474, phi_t49_3099044504245996706475, phi_t49_3099044504245996706476, phi_t49_6198089008491993412801, phi_t49_6198089008491993412802, phi_t49_6198089008491993412803, phi_t49_6198089008491993412804, phi_t49_6198089008491993412805, phi_t49_6198089008491993412806, phi_t49_6198089008491993412807, phi_t49_6198089008491993412808, phi_t49_6198089008491993412809, phi_t49_6198089008491993412810, phi_t49_6198089008491993412811, phi_t49_6198089008491993412812, phi_t49_6198089008491993412813, phi_t49_6198089008491993412814, phi_t49_6198089008491993412815, phi_t49_6198089008491993412816, phi_t49_6198089008491993412817, phi_t49_6198089008491993412818, phi_t49_6198089008491993412819, phi_t49_6198089008491993412820, phi_t49_6198089008491993412821, phi_t49_6198089008491993412822, phi_t49_6198089008491993412823, phi_t49_6198089008491993412824, phi_t49_6198089008491993412825, phi_t49_6198089008491993412826, phi_t49_6198089008491993412827, phi_t49_6198089008491993412828, phi_t49_6198089008491993412829, phi_t49_6198089008491993412830, phi_t49_6198089008491993412831, phi_t49_6198089008491993412832, phi_t49_6198089008491993412833, phi_t49_6198089008491993412834, phi_t49_6198089008491993412835, phi_t49_6198089008491993412836, phi_t49_6198089008491993412837, phi_t49_6198089008491993412838, phi_t49_6198089008491993412839, phi_t49_6198089008491993412840, phi_t49_6198089008491993412841, phi_t49_6198089008491993412842, phi_t49_6198089008491993412843, phi_t49_6198089008491993412844, phi_t49_6198089008491993412845, phi_t49_6198089008491993412846, phi_t49_6198089008491993412847, phi_t49_6198089008491993412848, phi_t49_6198089008491993412849, phi_t49_6198089008491993412850, phi_t49_6198089008491993412851, phi_t49_6198089008491993412852, phi_t49_6198089008491993412853, phi_t49_6198089008491993412854, phi_t49_6198089008491993412855, phi_t49_6198089008491993412856, phi_t49_6198089008491993412857, phi_t49_6198089008491993412858, phi_t49_6198089008491993412859, phi_t49_6198089008491993412860, phi_t49_6198089008491993412861, phi_t49_6198089008491993412862, phi_t49_6198089008491993412863, phi_t49_6198089008491993412864, phi_t49_6198089008491993412865, phi_t49_6198089008491993412866, phi_t49_6198089008491993412867, phi_t49_6198089008491993412868, phi_t49_6198089008491993412869, phi_t49_6198089008491993412870, phi_t49_6198089008491993412871, phi_t49_6198089008491993412872, phi_t49_6198089008491993412873, phi_t49_6198089008491993412874, phi_t49_6198089008491993412875, phi_t49_6198089008491993412876]

def diagonalPincerCertificateScalesThroughT49 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49]

def diagonalPincerKillDepthThroughT49 : ℕ → ℕ
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
  | _ => 0

/-- All 24 imported scales through t=49 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t49 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT49,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT49 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT49, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t37
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t41
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t43
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t47
  · simpa [diagonalPincerKillDepthThroughT49] using certifiedKill_diagonal_t49

#print axioms certifiedKill_diagonal_all_imported_through_t49

end TotientTailPeriodKiller
end Erdos249257
