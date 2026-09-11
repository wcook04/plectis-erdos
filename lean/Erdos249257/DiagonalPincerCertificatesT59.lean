import Erdos249257.DiagonalPincerCertificatesT53
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64

/-!
# The t=59 diagonal-pincer certificate

This generated extension consumes 161 new large-prime Lucas roots
and 1081 recursive Pratt dependencies, reuses 0 earlier certificates,
reconstructs all 176 Euler totients in the t=59 window, and proves the
twenty-sixth finite diagonal kill without `native_decide`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=59 window -/

private theorem prime_t59_2 : Nat.Prime 2 := by norm_num
private theorem prime_t59_3 : Nat.Prime 3 := by norm_num
private theorem prime_t59_5 : Nat.Prime 5 := by norm_num
private theorem prime_t59_7 : Nat.Prime 7 := by norm_num
private theorem prime_t59_11 : Nat.Prime 11 := by norm_num
private theorem prime_t59_13 : Nat.Prime 13 := by norm_num
private theorem prime_t59_17 : Nat.Prime 17 := by norm_num
private theorem prime_t59_19 : Nat.Prime 19 := by norm_num
private theorem prime_t59_23 : Nat.Prime 23 := by norm_num
private theorem prime_t59_29 : Nat.Prime 29 := by norm_num
private theorem prime_t59_31 : Nat.Prime 31 := by norm_num
private theorem prime_t59_37 : Nat.Prime 37 := by norm_num
private theorem prime_t59_41 : Nat.Prime 41 := by norm_num
private theorem prime_t59_43 : Nat.Prime 43 := by norm_num
private theorem prime_t59_47 : Nat.Prime 47 := by norm_num
private theorem prime_t59_53 : Nat.Prime 53 := by norm_num
private theorem prime_t59_59 : Nat.Prime 59 := by norm_num
private theorem prime_t59_61 : Nat.Prime 61 := by norm_num
private theorem prime_t59_67 : Nat.Prime 67 := by norm_num
private theorem prime_t59_71 : Nat.Prime 71 := by norm_num
private theorem prime_t59_73 : Nat.Prime 73 := by norm_num
private theorem prime_t59_79 : Nat.Prime 79 := by norm_num
private theorem prime_t59_83 : Nat.Prime 83 := by norm_num
private theorem prime_t59_89 : Nat.Prime 89 := by norm_num
private theorem prime_t59_97 : Nat.Prime 97 := by norm_num
private theorem prime_t59_101 : Nat.Prime 101 := by norm_num
private theorem prime_t59_103 : Nat.Prime 103 := by norm_num
private theorem prime_t59_107 : Nat.Prime 107 := by norm_num
private theorem prime_t59_109 : Nat.Prime 109 := by norm_num
private theorem prime_t59_113 : Nat.Prime 113 := by norm_num
private theorem prime_t59_127 : Nat.Prime 127 := by norm_num
private theorem prime_t59_131 : Nat.Prime 131 := by norm_num
private theorem prime_t59_137 : Nat.Prime 137 := by norm_num
private theorem prime_t59_139 : Nat.Prime 139 := by norm_num
private theorem prime_t59_149 : Nat.Prime 149 := by norm_num
private theorem prime_t59_151 : Nat.Prime 151 := by norm_num
private theorem prime_t59_157 : Nat.Prime 157 := by norm_num
private theorem prime_t59_163 : Nat.Prime 163 := by norm_num
private theorem prime_t59_167 : Nat.Prime 167 := by norm_num
private theorem prime_t59_181 : Nat.Prime 181 := by norm_num
private theorem prime_t59_193 : Nat.Prime 193 := by norm_num
private theorem prime_t59_197 : Nat.Prime 197 := by norm_num
private theorem prime_t59_199 : Nat.Prime 199 := by norm_num
private theorem prime_t59_211 : Nat.Prime 211 := by norm_num
private theorem prime_t59_223 : Nat.Prime 223 := by norm_num
private theorem prime_t59_227 : Nat.Prime 227 := by norm_num
private theorem prime_t59_239 : Nat.Prime 239 := by norm_num
private theorem prime_t59_251 : Nat.Prime 251 := by norm_num
private theorem prime_t59_257 : Nat.Prime 257 := by norm_num
private theorem prime_t59_269 : Nat.Prime 269 := by norm_num
private theorem prime_t59_277 : Nat.Prime 277 := by norm_num
private theorem prime_t59_283 : Nat.Prime 283 := by norm_num
private theorem prime_t59_313 : Nat.Prime 313 := by norm_num
private theorem prime_t59_317 : Nat.Prime 317 := by norm_num
private theorem prime_t59_349 : Nat.Prime 349 := by norm_num
private theorem prime_t59_353 : Nat.Prime 353 := by norm_num
private theorem prime_t59_367 : Nat.Prime 367 := by norm_num
private theorem prime_t59_373 : Nat.Prime 373 := by norm_num
private theorem prime_t59_389 : Nat.Prime 389 := by norm_num
private theorem prime_t59_431 : Nat.Prime 431 := by norm_num
private theorem prime_t59_433 : Nat.Prime 433 := by norm_num
private theorem prime_t59_439 : Nat.Prime 439 := by norm_num
private theorem prime_t59_467 : Nat.Prime 467 := by norm_num
private theorem prime_t59_479 : Nat.Prime 479 := by norm_num
private theorem prime_t59_499 : Nat.Prime 499 := by norm_num
private theorem prime_t59_541 : Nat.Prime 541 := by norm_num
private theorem prime_t59_547 : Nat.Prime 547 := by norm_num
private theorem prime_t59_563 : Nat.Prime 563 := by norm_num
private theorem prime_t59_601 : Nat.Prime 601 := by norm_num
private theorem prime_t59_631 : Nat.Prime 631 := by norm_num
private theorem prime_t59_641 : Nat.Prime 641 := by norm_num
private theorem prime_t59_643 : Nat.Prime 643 := by norm_num
private theorem prime_t59_761 : Nat.Prime 761 := by norm_num
private theorem prime_t59_797 : Nat.Prime 797 := by norm_num
private theorem prime_t59_881 : Nat.Prime 881 := by norm_num
private theorem prime_t59_883 : Nat.Prime 883 := by norm_num
private theorem prime_t59_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_t59_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_t59_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_t59_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_t59_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_t59_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_t59_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_t59_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_t59_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_t59_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_t59_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_t59_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_t59_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_t59_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_t59_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_t59_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_t59_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_t59_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_t59_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_t59_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_t59_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_t59_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_t59_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_t59_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_t59_2657 : Nat.Prime 2657 := by norm_num
private theorem prime_t59_2693 : Nat.Prime 2693 := by norm_num
private theorem prime_t59_2729 : Nat.Prime 2729 := by norm_num
private theorem prime_t59_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_t59_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_t59_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_t59_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_t59_3037 : Nat.Prime 3037 := by norm_num
private theorem prime_t59_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_t59_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_t59_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_t59_3499 : Nat.Prime 3499 := by norm_num
private theorem prime_t59_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_t59_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_t59_3847 : Nat.Prime 3847 := by norm_num
private theorem prime_t59_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_t59_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_t59_4409 : Nat.Prime 4409 := by norm_num
private theorem prime_t59_4583 : Nat.Prime 4583 := by norm_num
private theorem prime_t59_4591 : Nat.Prime 4591 := by norm_num
private theorem prime_t59_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_t59_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_t59_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_t59_5087 : Nat.Prime 5087 := by norm_num
private theorem prime_t59_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_t59_5351 : Nat.Prime 5351 := by norm_num
private theorem prime_t59_5869 : Nat.Prime 5869 := by norm_num
private theorem prime_t59_6113 : Nat.Prime 6113 := by norm_num
private theorem prime_t59_6551 : Nat.Prime 6551 := by norm_num
private theorem prime_t59_6599 : Nat.Prime 6599 := by norm_num
private theorem prime_t59_7541 : Nat.Prime 7541 := by norm_num
private theorem prime_t59_8069 : Nat.Prime 8069 := by norm_num
private theorem prime_t59_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_t59_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_t59_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_t59_8867 : Nat.Prime 8867 := by norm_num
private theorem prime_t59_9767 : Nat.Prime 9767 := by norm_num
private theorem prime_t59_10667 : Nat.Prime 10667 := by norm_num
private theorem prime_t59_10771 : Nat.Prime 10771 := by norm_num
private theorem prime_t59_12011 : Nat.Prime 12011 := by norm_num
private theorem prime_t59_12503 : Nat.Prime 12503 := by norm_num
private theorem prime_t59_13721 : Nat.Prime 13721 := by norm_num
private theorem prime_t59_13967 : Nat.Prime 13967 := by norm_num
private theorem prime_t59_15227 : Nat.Prime 15227 := by norm_num
private theorem prime_t59_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_t59_20663 : Nat.Prime 20663 := by norm_num
private theorem prime_t59_22573 : Nat.Prime 22573 := by norm_num
private theorem prime_t59_23561 : Nat.Prime 23561 := by norm_num
private theorem prime_t59_24889 : Nat.Prime 24889 := by norm_num
private theorem prime_t59_25633 : Nat.Prime 25633 := by norm_num
private theorem prime_t59_27983 : Nat.Prime 27983 := by norm_num
private theorem prime_t59_37897 : Nat.Prime 37897 := by norm_num
private theorem prime_t59_39799 : Nat.Prime 39799 := by norm_num
private theorem prime_t59_42071 : Nat.Prime 42071 := by norm_num
private theorem prime_t59_42929 : Nat.Prime 42929 := by norm_num
private theorem prime_t59_49069 : Nat.Prime 49069 := by norm_num
private theorem prime_t59_51199 : Nat.Prime 51199 := by norm_num
private theorem prime_t59_51241 : Nat.Prime 51241 := by norm_num
private theorem prime_t59_58997 : Nat.Prime 58997 := by norm_num
private theorem prime_t59_66499 : Nat.Prime 66499 := by norm_num
private theorem prime_t59_85447 : Nat.Prime 85447 := by norm_num
private theorem prime_t59_90599 : Nat.Prime 90599 := by norm_num
private theorem prime_t59_94427 : Nat.Prime 94427 := by norm_num
private theorem prime_t59_106109 : Nat.Prime 106109 := by norm_num
private theorem prime_t59_121327 : Nat.Prime 121327 := by norm_num
private theorem prime_t59_128833 : Nat.Prime 128833 := by norm_num
private theorem prime_t59_143501 : Nat.Prime 143501 := by norm_num
private theorem prime_t59_172259 : Nat.Prime 172259 := by norm_num
private theorem prime_t59_181757 : Nat.Prime 181757 := by norm_num
private theorem prime_t59_185519 : Nat.Prime 185519 := by norm_num
private theorem prime_t59_191473 : Nat.Prime 191473 := by norm_num
private theorem prime_t59_202753 : Nat.Prime 202753 := by norm_num
private theorem prime_t59_249037 : Nat.Prime 249037 := by norm_num
private theorem prime_t59_271919 : Nat.Prime 271919 := by norm_num
private theorem prime_t59_314761 : Nat.Prime 314761 := by norm_num
private theorem prime_t59_323249 : Nat.Prime 323249 := by norm_num
private theorem prime_t59_333209 : Nat.Prime 333209 := by norm_num
private theorem prime_t59_341557 : Nat.Prime 341557 := by norm_num
private theorem prime_t59_408713 : Nat.Prime 408713 := by norm_num
private theorem prime_t59_478913 : Nat.Prime 478913 := by norm_num
private theorem prime_t59_480499 : Nat.Prime 480499 := by norm_num
private theorem prime_t59_504607 : Nat.Prime 504607 := by norm_num
private theorem prime_t59_558413 : Nat.Prime 558413 := by norm_num
private theorem prime_t59_613219 : Nat.Prime 613219 := by norm_num
private theorem prime_t59_679867 : Nat.Prime 679867 := by norm_num
private theorem prime_t59_690839 : Nat.Prime 690839 := by norm_num
private theorem prime_t59_709351 : Nat.Prime 709351 := by norm_num
private theorem prime_t59_731827 : Nat.Prime 731827 := by norm_num
private theorem prime_t59_822949 : Nat.Prime 822949 := by norm_num
private theorem prime_t59_856391 : Nat.Prime 856391 := by norm_num
private theorem prime_t59_952363 : Nat.Prime 952363 := by norm_num
private theorem prime_t59_1260011 : Nat.Prime 1260011 := by norm_num
private theorem prime_t59_1560893 : Nat.Prime 1560893 := by norm_num
private theorem prime_t59_1654427 : Nat.Prime 1654427 := by norm_num
private theorem prime_t59_1750733 : Nat.Prime 1750733 := by norm_num
private theorem prime_t59_2086159 : Nat.Prime 2086159 := by norm_num
private theorem prime_t59_2170607 : Nat.Prime 2170607 := by norm_num
private theorem prime_t59_2443277 : Nat.Prime 2443277 := by norm_num
private theorem prime_t59_2584999 : Nat.Prime 2584999 := by norm_num
private theorem prime_t59_2886839 : Nat.Prime 2886839 := by norm_num
private theorem prime_t59_3498343 : Nat.Prime 3498343 := by norm_num
private theorem prime_t59_3754141 : Nat.Prime 3754141 := by norm_num
private theorem prime_t59_3993547 : Nat.Prime 3993547 := by norm_num
private theorem prime_t59_5569273 : Nat.Prime 5569273 := by norm_num
private theorem prime_t59_6138113 : Nat.Prime 6138113 := by norm_num
private theorem prime_t59_6941941 : Nat.Prime 6941941 := by norm_num
private theorem prime_t59_8904143 : Nat.Prime 8904143 := by norm_num
private theorem prime_t59_9237737 : Nat.Prime 9237737 := by norm_num
private theorem prime_t59_9483251 : Nat.Prime 9483251 := by norm_num
private theorem prime_t59_9609673 : Nat.Prime 9609673 := by norm_num
private theorem prime_t59_10024009 : Nat.Prime 10024009 := by norm_num
private theorem prime_t59_10144217 : Nat.Prime 10144217 := by norm_num
private theorem prime_t59_11828867 : Nat.Prime 11828867 := by norm_num
private theorem prime_t59_14350759 : Nat.Prime 14350759 := by norm_num
private theorem prime_t59_14503187 : Nat.Prime 14503187 := by norm_num
private theorem prime_t59_14641873 : Nat.Prime 14641873 := by norm_num
private theorem prime_t59_15877079 : Nat.Prime 15877079 := by norm_num
private theorem prime_t59_19364897 : Nat.Prime 19364897 := by norm_num
private theorem prime_t59_25248323 : Nat.Prime 25248323 := by norm_num
private theorem prime_t59_31327579 : Nat.Prime 31327579 := by norm_num

/-! ## Exact t=59 window totients -/

private theorem phi_t59_9690712164777231700912801 : Nat.totient 9690712164777231700912801 = 9650165251953896003419204 := by
  rw [← show ((([(239, 1), (40546912823335697493359, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_239, prime_lucas_40546912823335697493359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912802 : Nat.totient 9690712164777231700912802 = 4822698937234206410426880 := by
  rw [← show ((([(2, 1), (353, 1), (541, 1), (25371943062048644837, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_353, prime_t59_541, prime_lucas_25371943062048644837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912803 : Nat.totient 9690712164777231700912803 = 6443615459692666083409920 := by
  rw [← show ((([(3, 1), (389, 1), (25633, 1), (473936833, 1), (683541581, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_389, prime_t59_25633, prime_lucas_473936833, prime_lucas_683541581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912804 : Nat.totient 9690712164777231700912804 = 4845356082388615850456400 := by
  rw [← show ((([(2, 2), (2422678041194307925228201, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_lucas_2422678041194307925228201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912805 : Nat.totient 9690712164777231700912805 = 7748430574763277449526528 := by
  rw [← show ((([(5, 1), (1873, 1), (203158463, 1), (5093461104239, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_1873, prime_lucas_203158463, prime_lucas_5093461104239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912806 : Nat.totient 9690712164777231700912806 = 3176194131549209727781440 := by
  rw [← show ((([(2, 1), (3, 1), (83, 1), (211, 1), (92223987559500863177, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_83, prime_t59_211, prime_lucas_92223987559500863177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912807 : Nat.totient 9690712164777231700912807 = 8306299016299890686989824 := by
  rw [← show ((([(7, 1), (323249, 1), (4282727717985308849, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_7, prime_t59_323249, prime_lucas_4282727717985308849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912808 : Nat.totient 9690712164777231700912808 = 4773030133734756198835200 := by
  rw [← show ((([(2, 3), (67, 1), (709351, 1), (10144217, 1), (2512529609, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_67, prime_t59_709351, prime_t59_10144217, prime_lucas_2512529609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912809 : Nat.totient 9690712164777231700912809 = 6400096507578732462907512 := by
  rw [← show ((([(3, 2), (107, 1), (10063044823237000727843, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_107, prime_lucas_10063044823237000727843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912810 : Nat.totient 9690712164777231700912810 = 3874681107174479402457088 := by
  rw [← show ((([(2, 1), (5, 1), (2417, 1), (400939684103319474593, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_2417, prime_lucas_400939684103319474593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912811 : Nat.totient 9690712164777231700912811 = 8795994590068682865664000 := by
  rw [← show ((([(11, 1), (641, 1), (1374374154698231697761, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_11, prime_t59_641, prime_lucas_1374374154698231697761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912812 : Nat.totient 9690712164777231700912812 = 3228067987729689001775616 := by
  rw [← show ((([(2, 2), (3, 1), (1489, 1), (542350132347057964009, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_1489, prime_lucas_542350132347057964009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912813 : Nat.totient 9690712164777231700912813 = 8913645478944131835377664 := by
  rw [← show ((([(13, 1), (283, 1), (480499, 1), (5481929149748353, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_13, prime_t59_283, prime_t59_480499, prime_lucas_5481929149748353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912814 : Nat.totient 9690712164777231700912814 = 4153162344312962119325400 := by
  rw [← show ((([(2, 1), (7, 1), (345517111, 1), (2003355851327191, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_7, prime_lucas_345517111, prime_lucas_2003355851327191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912815 : Nat.totient 9690712164777231700912815 = 5168379818904799327164576 := by
  rw [← show ((([(3, 1), (5, 1), (2237678323, 1), (288713293153627, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_5, prime_lucas_2237678323, prime_lucas_288713293153627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912816 : Nat.totient 9690712164777231700912816 = 4842698162933997575856960 := by
  rw [← show ((([(2, 4), (1823, 1), (284086967, 1), (1169493285811, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_1823, prime_lucas_284086967, prime_lucas_1169493285811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912817 : Nat.totient 9690712164777231700912817 = 9084329222873882770848000 := by
  rw [← show ((([(17, 1), (251, 1), (2443277, 1), (929523437269663, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_17, prime_t59_251, prime_t59_2443277, prime_lucas_929523437269663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912818 : Nat.totient 9690712164777231700912818 = 3222054813755992607850240 := by
  rw [← show ((([(2, 1), (3, 2), (479, 1), (2381, 1), (37897, 1), (12456139076467, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_479, prime_t59_2381, prime_t59_37897, prime_lucas_12456139076467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912819 : Nat.totient 9690712164777231700912819 = 9164353033143327961267632 := by
  rw [← show ((([(19, 2), (563, 1), (613219, 1), (77754314149907, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_19, prime_t59_563, prime_t59_613219, prime_lucas_77754314149907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912820 : Nat.totient 9690712164777231700912820 = 3826862642723375236775040 := by
  rw [← show ((([(2, 2), (5, 1), (79, 1), (10771, 1), (569432933767137949, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_79, prime_t59_10771, prime_lucas_569432933767137949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912821 : Nat.totient 9690712164777231700912821 = 5537548421819708389607664 := by
  rw [← show ((([(3, 1), (7, 1), (3993547, 1), (115552035330249283, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_7, prime_t59_3993547, prime_lucas_115552035330249283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912822 : Nat.totient 9690712164777231700912822 = 4400917061659411482989280 := by
  rw [← show ((([(2, 1), (11, 1), (1427, 1), (5087, 1), (60680241799800949, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_11, prime_t59_1427, prime_t59_5087, prime_lucas_60680241799800949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912823 : Nat.totient 9690712164777231700912823 = 9269376828293239219720224 := by
  rw [← show ((([(23, 1), (371191837, 1), (1135087761943573, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_23, prime_lucas_371191837, prime_lucas_1135087761943573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912824 : Nat.totient 9690712164777231700912824 = 3230094061354473172734336 := by
  rw [← show ((([(2, 3), (3, 1), (22573, 1), (14350759, 1), (1246465607143, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_22573, prime_t59_14350759, prime_lucas_1246465607143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912825 : Nat.totient 9690712164777231700912825 = 7672646332524653552885760 := by
  rw [← show ((([(5, 2), (97, 1), (3996169964856590392129, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_97, prime_lucas_3996169964856590392129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912826 : Nat.totient 9690712164777231700912826 = 4472623288897137089365824 := by
  rw [← show ((([(2, 1), (13, 1), (341557, 1), (1091237183384554093, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_13, prime_t59_341557, prime_lucas_1091237183384554093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912827 : Nat.totient 9690712164777231700912827 = 6460474776518154467275164 := by
  rw [← show ((([(3, 4), (119638421787373230875467, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_lucas_119638421787373230875467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912828 : Nat.totient 9690712164777231700912828 = 4153157220212340767184960 := by
  rw [← show ((([(2, 2), (7, 1), (856391, 1), (14503187, 1), (27865197253, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_7, prime_t59_856391, prime_t59_14503187, prime_lucas_27865197253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912829 : Nat.totient 9690712164777231700912829 = 9224587259455319267376000 := by
  rw [← show ((([(29, 1), (71, 1), (51241, 1), (91850547836664191, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_29, prime_t59_71, prime_t59_51241, prime_lucas_91850547836664191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912830 : Nat.totient 9690712164777231700912830 = 2566845465005568158832000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (149, 1), (2886839, 1), (750975220952251, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_5, prime_t59_149, prime_t59_2886839, prime_lucas_750975220952251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912831 : Nat.totient 9690712164777231700912831 = 9175910174796016668556800 := by
  rw [← show ((([(31, 1), (73, 1), (131, 1), (2939, 1), (11122444788201193, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_31, prime_t59_73, prime_t59_131, prime_t59_2939, prime_lucas_11122444788201193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912832 : Nat.totient 9690712164777231700912832 = 4790913879215710054381056 := by
  rw [← show ((([(2, 6), (89, 1), (1701318849153306127267, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_89, prime_lucas_1701318849153306127267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912833 : Nat.totient 9690712164777231700912833 = 5861389030253308297764480 := by
  rw [← show ((([(3, 1), (11, 2), (499, 1), (53499352229402229809, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_11, prime_t59_499, prime_lucas_53499352229402229809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912834 : Nat.totient 9690712164777231700912834 = 4533477902722230076200960 := by
  rw [← show ((([(2, 1), (17, 1), (181, 1), (2729, 1), (25248323, 1), (22853995063, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_17, prime_t59_181, prime_t59_2729, prime_t59_25248323, prime_lucas_22853995063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912835 : Nat.totient 9690712164777231700912835 = 6644901821432663356360800 := by
  rw [← show ((([(5, 1), (7, 1), (42071, 1), (6581195845646802311, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_7, prime_t59_42071, prime_lucas_6581195845646802311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912836 : Nat.totient 9690712164777231700912836 = 3229357933484163245781504 := by
  rw [← show ((([(2, 2), (3, 2), (3673, 1), (73287897909498984337, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_3673, prime_lucas_73287897909498984337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912837 : Nat.totient 9690712164777231700912837 = 9428690520028407511401408 := by
  rw [← show ((([(37, 1), (85447, 1), (59599717, 1), (51429577099, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_37, prime_t59_85447, prime_lucas_59599717, prime_lucas_51429577099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912838 : Nat.totient 9690712164777231700912838 = 4536356921619139130400000 := by
  rw [← show ((([(2, 1), (19, 1), (103, 1), (1151, 1), (1307, 1), (2281, 1), (721537116451, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_19, prime_t59_103, prime_t59_1151, prime_t59_1307, prime_t59_2281, prime_lucas_721537116451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912839 : Nat.totient 9690712164777231700912839 = 5920400612536006123837440 := by
  rw [← show ((([(3, 1), (13, 2), (139, 1), (27983, 1), (4914039716240321, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_13, prime_t59_139, prime_t59_27983, prime_lucas_4914039716240321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912840 : Nat.totient 9690712164777231700912840 = 3876262339141202801245440 := by
  rw [← show ((([(2, 3), (5, 1), (172259, 1), (163810411, 1), (8585632229, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_172259, prime_lucas_163810411, prime_lucas_8585632229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912841 : Nat.totient 9690712164777231700912841 = 9454353331150443547566880 := by
  rw [← show ((([(41, 1), (27936651683, 1), (8460528339947, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_41, prime_lucas_27936651683, prime_lucas_8460528339947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912842 : Nat.totient 9690712164777231700912842 = 2768774904222066200260800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (230731242018505516688401, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_7, prime_lucas_230731242018505516688401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912843 : Nat.totient 9690712164777231700912843 = 9464847512114346944457768 := by
  rw [← show ((([(43, 1), (18959, 1), (11886987667116717839, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_43, prime_t59_18959, prime_lucas_11886987667116717839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912844 : Nat.totient 9690712164777231700912844 = 4404324615286654715950080 := by
  rw [← show ((([(2, 2), (11, 1), (8089, 1), (27227526058893760609, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_11, prime_t59_8089, prime_lucas_27227526058893760609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912845 : Nat.totient 9690712164777231700912845 = 5078818237937570972352000 := by
  rw [← show ((([(3, 2), (5, 1), (61, 1), (1327, 1), (5351, 1), (94427, 1), (5265156439, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_5, prime_t59_61, prime_t59_1327, prime_t59_5351, prime_t59_94427, prime_lucas_5265156439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912846 : Nat.totient 9690712164777231700912846 = 4634688426531469668172800 := by
  rw [← show ((([(2, 1), (23, 1), (46300212961, 1), (4550036431441, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_23, prime_lucas_46300212961, prime_lucas_4550036431441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912847 : Nat.totient 9690712164777231700912847 = 9409282891548288209568000 := by
  rw [← show ((([(47, 1), (151, 1), (761, 1), (181757, 1), (9871998630763, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_47, prime_t59_151, prime_t59_761, prime_t59_181757, prime_lucas_9871998630763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912848 : Nat.totient 9690712164777231700912848 = 3230236464896963097061632 := by
  rw [← show ((([(2, 4), (3, 1), (3498343, 1), (57710132130037657, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_3498343, prime_lucas_57710132130037657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912849 : Nat.totient 9690712164777231700912849 = 8297398467581091426933984 := by
  rw [← show ((([(7, 2), (1303, 1), (3253, 1), (46658538942590539, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_7, prime_t59_1303, prime_t59_3253, prime_lucas_46658538942590539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912850 : Nat.totient 9690712164777231700912850 = 3876187428873973551602880 := by
  rw [← show ((([(2, 1), (5, 2), (39799, 1), (95894597, 1), (50783121419, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_39799, prime_lucas_95894597, prime_lucas_50783121419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912851 : Nat.totient 9690712164777231700912851 = 6032569314247614361286784 := by
  rw [← show ((([(3, 1), (17, 1), (127, 1), (1496172945001888482463, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_17, prime_t59_127, prime_lucas_1496172945001888482463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912852 : Nat.totient 9690712164777231700912852 = 4471358122416174707827296 := by
  rw [← show ((([(2, 2), (13, 1), (3499, 1), (53260888631791675099, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_13, prime_t59_3499, prime_lucas_53260888631791675099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912853 : Nat.totient 9690712164777231700912853 = 9480625362697128445660608 := by
  rw [← show ((([(53, 1), (349, 1), (523907237107489414549, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_53, prime_t59_349, prime_lucas_523907237107489414549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912854 : Nat.totient 9690712164777231700912854 = 3211683811789544542431360 := by
  rw [← show ((([(2, 1), (3, 3), (277, 1), (467, 1), (72923491, 1), (19023824629, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_277, prime_t59_467, prime_lucas_72923491, prime_lucas_19023824629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912855 : Nat.totient 9690712164777231700912855 = 7047647022221160860620800 := by
  rw [← show ((([(5, 1), (11, 1), (49069, 1), (603434549, 1), (5950529681, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_11, prime_t59_49069, prime_lucas_603434549, prime_lucas_5950529681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912856 : Nat.totient 9690712164777231700912856 = 4153162356333099300391200 := by
  rw [← show ((([(2, 3), (7, 1), (173048431513879137516301, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_7, prime_lucas_173048431513879137516301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912857 : Nat.totient 9690712164777231700912857 = 6120449631996084422636544 := by
  rw [← show ((([(3, 1), (19, 1), (39162289, 1), (4341229750868209, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_19, prime_lucas_39162289, prime_lucas_4341229750868209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912858 : Nat.totient 9690712164777231700912858 = 4667618175182989683378624 := by
  rw [← show ((([(2, 1), (29, 1), (439, 1), (16814770867, 1), (22634568877, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_29, prime_t59_439, prime_lucas_16814770867, prime_lucas_22634568877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912859 : Nat.totient 9690712164777231700912859 = 9524619919782456346667040 := by
  rw [← show ((([(59, 1), (5171, 1), (15877079, 1), (2000592052189, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_59, prime_t59_5171, prime_t59_15877079, prime_lucas_2000592052189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912860 : Nat.totient 9690712164777231700912860 = 2578335172403795165088000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (547, 1), (2791, 1), (12503, 1), (8461416048851, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_5, prime_t59_547, prime_t59_2791, prime_t59_12503, prime_lucas_8461416048851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912861 : Nat.totient 9690712164777231700912861 = 9658324606285236251535360 := by
  rw [← show ((([(313, 1), (8069, 1), (42929, 1), (2170607, 1), (41177471, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_313, prime_t59_8069, prime_t59_42929, prime_t59_2170607, prime_lucas_41177471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912862 : Nat.totient 9690712164777231700912862 = 4689054273279305661732000 := by
  rw [← show ((([(2, 1), (31, 1), (156301809109310188724401, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_31, prime_lucas_156301809109310188724401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912863 : Nat.totient 9690712164777231700912863 = 5482639951912387134432000 := by
  rw [← show ((([(3, 2), (7, 1), (101, 1), (66499, 1), (31327579, 1), (731057981, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_7, prime_t59_101, prime_t59_66499, prime_t59_31327579, prime_lucas_731057981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912864 : Nat.totient 9690712164777231700912864 = 4833427087525592331878400 := by
  rw [← show ((([(2, 5), (433, 1), (6551, 1), (5569273, 1), (19169540953, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_433, prime_t59_6551, prime_t59_5569273, prime_lucas_19169540953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912865 : Nat.totient 9690712164777231700912865 = 7156218213989340332981760 := by
  rw [← show ((([(5, 1), (13, 1), (149087879458111256937121, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_13, prime_lucas_149087879458111256937121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912866 : Nat.totient 9690712164777231700912866 = 2921339503847307317760000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (193, 1), (121327, 1), (6941941, 1), (903266851, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_11, prime_t59_193, prime_t59_121327, prime_t59_6941941, prime_lucas_903266851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912867 : Nat.totient 9690712164777231700912867 = 9685541217811337771719680 := by
  rw [← show ((([(2027, 1), (24889, 1), (10024009, 1), (19162538921, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2027, prime_t59_24889, prime_t59_10024009, prime_lucas_19162538921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912868 : Nat.totient 9690712164777231700912868 = 4539885199414892782640640 := by
  rw [← show ((([(2, 2), (17, 1), (223, 1), (1262847067, 1), (506047354261, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_17, prime_t59_223, prime_lucas_1262847067, prime_lucas_506047354261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912869 : Nat.totient 9690712164777231700912869 = 6118001693380981021818816 := by
  rw [← show ((([(3, 1), (23, 1), (163, 1), (367, 1), (883, 1), (2658840168703207, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_23, prime_t59_163, prime_t59_367, prime_t59_883, prime_lucas_2658840168703207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912870 : Nat.totient 9690712164777231700912870 = 3322475777710519247711232 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (106109, 1), (185519, 1), (731827, 1), (9609673, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_7, prime_t59_106109, prime_t59_185519, prime_t59_731827, prime_t59_9609673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912871 : Nat.totient 9690712164777231700912871 = 9690705956336188798120632 := by
  rw [← show ((([(1560893, 1), (6208441042901231347, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_1560893, prime_lucas_6208441042901231347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912872 : Nat.totient 9690712164777231700912872 = 3229572867093008713209600 := by
  rw [← show ((([(2, 3), (3, 2), (4861, 1), (27688381919521679641, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_4861, prime_lucas_27688381919521679641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912873 : Nat.totient 9690712164777231700912873 = 9688633950716588931939540 := by
  rw [← show ((([(4663, 1), (2078214060642768968671, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_4663, prime_lucas_2078214060642768968671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912874 : Nat.totient 9690712164777231700912874 = 4714399256807582219966400 := by
  rw [← show ((([(2, 1), (37, 1), (3754141, 1), (34882965182790661, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_37, prime_t59_3754141, prime_lucas_34882965182790661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912875 : Nat.totient 9690712164777231700912875 = 5090146579342722562790400 := by
  rw [← show ((([(3, 1), (5, 3), (67, 2), (4657, 1), (1236142628038037, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_5, prime_t59_67, prime_t59_4657, prime_lucas_1236142628038037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912876 : Nat.totient 9690712164777231700912876 = 4589123549561503119074880 := by
  rw [← show ((([(2, 2), (19, 1), (3847, 1), (271919, 1), (1260011, 1), (96739987, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_19, prime_t59_3847, prime_t59_271919, prime_t59_1260011, prime_lucas_96739987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912877 : Nat.totient 9690712164777231700912877 = 7551201363078669595968240 := by
  rw [← show ((([(7, 1), (11, 1), (2584999, 1), (48686055482948599, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_7, prime_t59_11, prime_t59_2584999, prime_lucas_48686055482948599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912878 : Nat.totient 9690712164777231700912878 = 2954843862189483737088000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (113, 1), (5869, 1), (128833, 1), (1454090438501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_13, prime_t59_113, prime_t59_5869, prime_t59_128833, prime_lucas_1454090438501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912879 : Nat.totient 9690712164777231700912879 = 9601806548586614896317240 := by
  rw [← show ((([(109, 1), (88905616190616804595531, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_109, prime_lucas_88905616190616804595531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912880 : Nat.totient 9690712164777231700912880 = 3875049199712004923592704 := by
  rw [← show ((([(2, 4), (5, 1), (3137, 1), (38614568715242396003, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_3137, prime_lucas_38614568715242396003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912881 : Nat.totient 9690712164777231700912881 = 6450244199218115429145408 := by
  rw [← show ((([(3, 3), (797, 1), (3037, 1), (148282130330738827, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_797, prime_t59_3037, prime_lucas_148282130330738827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912882 : Nat.totient 9690712164777231700912882 = 4727151954139975211950080 := by
  rw [← show ((([(2, 1), (41, 1), (191473, 1), (220484633, 1), (2799342089, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_41, prime_t59_191473, prime_lucas_220484633, prime_lucas_2799342089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912883 : Nat.totient 9690712164777231700912883 = 9642660840022333157160960 := by
  rw [← show ((([(269, 1), (1433, 1), (2111, 1), (13967, 1), (408713, 1), (2086159, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_269, prime_t59_1433, prime_t59_2111, prime_t59_13967, prime_t59_408713, prime_t59_2086159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912884 : Nat.totient 9690712164777231700912884 = 2767937613178893404578560 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (3307, 1), (62456483, 1), (558553385321, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_7, prime_t59_3307, prime_lucas_62456483, prime_lucas_558553385321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912885 : Nat.totient 9690712164777231700912885 = 7296057008857271819922432 := by
  rw [← show ((([(5, 1), (17, 1), (15227, 1), (292453927, 1), (25601473589, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_17, prime_t59_15227, prime_lucas_292453927, prime_lucas_25601473589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912886 : Nat.totient 9690712164777231700912886 = 4732279354542184406593800 := by
  rw [← show ((([(2, 1), (43, 1), (12011, 1), (9381625142821823891, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_43, prime_t59_12011, prime_lucas_9381625142821823891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912887 : Nat.totient 9690712164777231700912887 = 6237214411741414309232640 := by
  rw [← show ((([(3, 1), (29, 1), (13721, 1), (202753, 1), (40039015328777, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_29, prime_t59_13721, prime_t59_202753, prime_lucas_40039015328777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_9690712164777231700912888 : Nat.totient 9690712164777231700912888 = 4404649613348200785886080 := by
  rw [← show ((([(2, 3), (11, 1), (20663, 1), (690839, 1), (7714411471693, 1)] : List FactorBlock).map factorBlockValue).prod) = 9690712164777231700912888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_11, prime_t59_20663, prime_t59_690839, prime_lucas_7714411471693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825601 : Nat.totient 19381424329554463401825601 = 19381424329554463401825600 := by
  rw [← show ((([(19381424329554463401825601, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_19381424329554463401825601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825602 : Nat.totient 19381424329554463401825602 = 9650165251953896003419204 := by
  rw [← show ((([(2, 1), (239, 1), (40546912823335697493359, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_239, prime_lucas_40546912823335697493359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825603 : Nat.totient 19381424329554463401825603 = 12920401100902877996869440 := by
  rw [← show ((([(3, 1), (23561, 1), (269190287, 1), (1018617962743, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_23561, prime_lucas_269190287, prime_lucas_1018617962743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825604 : Nat.totient 19381424329554463401825604 = 9645397874468412820853760 := by
  rw [← show ((([(2, 2), (353, 1), (541, 1), (25371943062048644837, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_353, prime_t59_541, prime_lucas_25371943062048644837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825605 : Nat.totient 19381424329554463401825605 = 15495530359947938393179200 := by
  rw [← show ((([(5, 1), (1901, 1), (10667, 1), (191157469874119663, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_1901, prime_t59_10667, prime_lucas_191157469874119663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825606 : Nat.totient 19381424329554463401825606 = 6443615459692666083409920 := by
  rw [← show ((([(2, 1), (3, 1), (389, 1), (25633, 1), (473936833, 1), (683541581, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_389, prime_t59_25633, prime_lucas_473936833, prime_lucas_683541581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825607 : Nat.totient 19381424329554463401825607 = 16612649424812133718516224 := by
  rw [← show ((([(7, 1), (31942990609, 1), (86678637517489, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_7, prime_lucas_31942990609, prime_lucas_86678637517489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825608 : Nat.totient 19381424329554463401825608 = 9690712164777231700912800 := by
  rw [← show ((([(2, 3), (2422678041194307925228201, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_lucas_2422678041194307925228201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825609 : Nat.totient 19381424329554463401825609 = 12920930547922730780172792 := by
  rw [← show ((([(3, 2), (679867, 1), (3167518929691716403, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_679867, prime_lucas_3167518929691716403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825610 : Nat.totient 19381424329554463401825610 = 7748430574763277449526528 := by
  rw [← show ((([(2, 1), (5, 1), (1873, 1), (203158463, 1), (5093461104239, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_1873, prime_lucas_203158463, prime_lucas_5093461104239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825611 : Nat.totient 19381424329554463401825611 = 17619282185624919351792040 := by
  rw [← show ((([(11, 1), (90599, 1), (19447760641101259799, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_11, prime_t59_90599, prime_lucas_19447760641101259799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825612 : Nat.totient 19381424329554463401825612 = 6352388263098419455562880 := by
  rw [← show ((([(2, 2), (3, 1), (83, 1), (211, 1), (92223987559500863177, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_83, prime_t59_211, prime_lucas_92223987559500863177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825613 : Nat.totient 19381424329554463401825613 = 17883902183493598381314624 := by
  rw [← show ((([(13, 1), (2693, 1), (553612623312704258957, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_13, prime_t59_2693, prime_lucas_553612623312704258957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825614 : Nat.totient 19381424329554463401825614 = 8306299016299890686989824 := by
  rw [← show ((([(2, 1), (7, 1), (323249, 1), (4282727717985308849, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_7, prime_t59_323249, prime_lucas_4282727717985308849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825615 : Nat.totient 19381424329554463401825615 = 10336759642429047147640320 := by
  rw [← show ((([(3, 1), (5, 1), (1292094955303630893455041, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_5, prime_lucas_1292094955303630893455041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825616 : Nat.totient 19381424329554463401825616 = 9546060267469512397670400 := by
  rw [← show ((([(2, 4), (67, 1), (709351, 1), (10144217, 1), (2512529609, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_67, prime_t59_709351, prime_t59_10144217, prime_lucas_2512529609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825617 : Nat.totient 19381424329554463401825617 = 18241340545414800250002432 := by
  rw [← show ((([(17, 1), (443529845593, 1), (2570478166057, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_17, prime_lucas_443529845593, prime_lucas_2570478166057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825618 : Nat.totient 19381424329554463401825618 = 6400096507578732462907512 := by
  rw [← show ((([(2, 1), (3, 2), (107, 1), (10063044823237000727843, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_107, prime_lucas_10063044823237000727843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825619 : Nat.totient 19381424329554463401825619 = 18333009996541853167779840 := by
  rw [← show ((([(19, 1), (881, 1), (2473, 1), (478913, 1), (558413, 1), (1750733, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_19, prime_t59_881, prime_t59_2473, prime_t59_478913, prime_t59_558413, prime_t59_1750733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825620 : Nat.totient 19381424329554463401825620 = 7749362214348958804914176 := by
  rw [← show ((([(2, 2), (5, 1), (2417, 1), (400939684103319474593, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_2417, prime_lucas_400939684103319474593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825621 : Nat.totient 19381424329554463401825621 = 11075099615438787303331824 := by
  rw [← show ((([(3, 1), (7, 1), (7641236443, 1), (120782150239507, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_7, prime_lucas_7641236443, prime_lucas_120782150239507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825622 : Nat.totient 19381424329554463401825622 = 8795994590068682865664000 := by
  rw [← show ((([(2, 1), (11, 1), (641, 1), (1374374154698231697761, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_11, prime_t59_641, prime_lucas_1374374154698231697761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825623 : Nat.totient 19381424329554463401825623 = 18538753704537826969944064 := by
  rw [← show ((([(23, 1), (9305086913, 1), (90560209797377, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_23, prime_lucas_9305086913, prime_lucas_90560209797377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825624 : Nat.totient 19381424329554463401825624 = 6456135975459378003551232 := by
  rw [← show ((([(2, 3), (3, 1), (1489, 1), (542350132347057964009, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_1489, prime_lucas_542350132347057964009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825625 : Nat.totient 19381424329554463401825625 = 15337181440896279024600000 := by
  rw [← show ((([(5, 4), (101, 1), (1063, 1), (288835808679779267, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_101, prime_t59_1063, prime_lucas_288835808679779267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825626 : Nat.totient 19381424329554463401825626 = 8913645478944131835377664 := by
  rw [← show ((([(2, 1), (13, 1), (283, 1), (480499, 1), (5481929149748353, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_13, prime_t59_283, prime_t59_480499, prime_lucas_5481929149748353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825627 : Nat.totient 19381424329554463401825627 = 12855360976624957112544096 := by
  rw [← show ((([(3, 3), (197, 1), (3643809800630656777933, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_197, prime_lucas_3643809800630656777933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825628 : Nat.totient 19381424329554463401825628 = 8306324688625924238650800 := by
  rw [← show ((([(2, 2), (7, 1), (345517111, 1), (2003355851327191, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_7, prime_lucas_345517111, prime_lucas_2003355851327191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825629 : Nat.totient 19381424329554463401825629 = 18397058519107959765984000 := by
  rw [← show ((([(29, 1), (61, 1), (3511, 1), (4583, 1), (1654427, 1), (411556591, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_29, prime_t59_61, prime_t59_3511, prime_t59_4583, prime_t59_1654427, prime_lucas_411556591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825630 : Nat.totient 19381424329554463401825630 = 5168379818904799327164576 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (2237678323, 1), (288713293153627, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_5, prime_lucas_2237678323, prime_lucas_288713293153627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825631 : Nat.totient 19381424329554463401825631 = 18756194301647650246281120 := by
  rw [← show ((([(31, 1), (822949, 1), (759715652412531949, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_31, prime_t59_822949, prime_lucas_759715652412531949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825632 : Nat.totient 19381424329554463401825632 = 9685396325867995151713920 := by
  rw [← show ((([(2, 5), (1823, 1), (284086967, 1), (1169493285811, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_1823, prime_lucas_284086967, prime_lucas_1169493285811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825633 : Nat.totient 19381424329554463401825633 = 11739379607870608772591040 := by
  rw [← show ((([(3, 1), (11, 1), (1693, 1), (346908380847240211957, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_11, prime_t59_1693, prime_lucas_346908380847240211957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825634 : Nat.totient 19381424329554463401825634 = 9084329222873882770848000 := by
  rw [← show ((([(2, 1), (17, 1), (251, 1), (2443277, 1), (929523437269663, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_17, prime_t59_251, prime_t59_2443277, prime_lucas_929523437269663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825635 : Nat.totient 19381424329554463401825635 = 13290119540180758620547200 := by
  rw [← show ((([(5, 1), (7, 1), (163605732541, 1), (3384691796821, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_7, prime_lucas_163605732541, prime_lucas_3384691796821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825636 : Nat.totient 19381424329554463401825636 = 6444109627511985215700480 := by
  rw [← show ((([(2, 2), (3, 2), (479, 1), (2381, 1), (37897, 1), (12456139076467, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_479, prime_t59_2381, prime_t59_37897, prime_lucas_12456139076467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825637 : Nat.totient 19381424329554463401825637 = 18720502183878738950640960 := by
  rw [← show ((([(37, 1), (157, 1), (1103, 1), (3024884531342705531, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_37, prime_t59_157, prime_t59_1103, prime_lucas_3024884531342705531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825638 : Nat.totient 19381424329554463401825638 = 9164353033143327961267632 := by
  rw [← show ((([(2, 1), (19, 2), (563, 1), (613219, 1), (77754314149907, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_19, prime_t59_563, prime_t59_613219, prime_lucas_77754314149907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825639 : Nat.totient 19381424329554463401825639 = 11845030450314641762007936 := by
  rw [← show ((([(3, 1), (13, 1), (167, 1), (1123, 1), (504607, 1), (5251357495523, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_13, prime_t59_167, prime_t59_1123, prime_t59_504607, prime_lucas_5251357495523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825640 : Nat.totient 19381424329554463401825640 = 7653725285446750473550080 := by
  rw [← show ((([(2, 3), (5, 1), (79, 1), (10771, 1), (569432933767137949, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_79, prime_t59_10771, prime_lucas_569432933767137949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825641 : Nat.totient 19381424329554463401825641 = 18835129813560410907648000 := by
  rw [← show ((([(41, 1), (257, 1), (8904143, 1), (206574439834351, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_41, prime_t59_257, prime_t59_8904143, prime_lucas_206574439834351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825642 : Nat.totient 19381424329554463401825642 = 5537548421819708389607664 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (3993547, 1), (115552035330249283, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_7, prime_t59_3993547, prime_lucas_115552035330249283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825643 : Nat.totient 19381424329554463401825643 = 18582991599591941159500800 := by
  rw [← show ((([(43, 1), (113, 1), (137, 1), (431, 1), (67552426492369991, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_43, prime_t59_113, prime_t59_137, prime_t59_431, prime_lucas_67552426492369991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825644 : Nat.totient 19381424329554463401825644 = 8801834123318822965978560 := by
  rw [← show ((([(2, 2), (11, 1), (1427, 1), (5087, 1), (60680241799800949, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_11, prime_t59_1427, prime_t59_5087, prime_lucas_60680241799800949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825645 : Nat.totient 19381424329554463401825645 = 10335503240963312295663360 := by
  rw [← show ((([(3, 2), (5, 1), (8233, 1), (11828867, 1), (4422541449971, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_5, prime_t59_8233, prime_t59_11828867, prime_lucas_4422541449971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825646 : Nat.totient 19381424329554463401825646 = 9269376828293239219720224 := by
  rw [← show ((([(2, 1), (23, 1), (371191837, 1), (1135087761943573, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_23, prime_lucas_371191837, prime_lucas_1135087761943573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825647 : Nat.totient 19381424329554463401825647 = 18883292732907952369580448 := by
  rw [← show ((([(47, 1), (227, 1), (8597, 1), (211307566268149279, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_47, prime_t59_227, prime_t59_8597, prime_lucas_211307566268149279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825648 : Nat.totient 19381424329554463401825648 = 6460188122708946345468672 := by
  rw [← show ((([(2, 4), (3, 1), (22573, 1), (14350759, 1), (1246465607143, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_22573, prime_t59_14350759, prime_lucas_1246465607143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825649 : Nat.totient 19381424329554463401825649 = 16460239694646216912468480 := by
  rw [← show ((([(7, 2), (109, 1), (159916661, 1), (22691823592049, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_7, prime_t59_109, prime_lucas_159916661, prime_lucas_22691823592049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825650 : Nat.totient 19381424329554463401825650 = 7672646332524653552885760 := by
  rw [← show ((([(2, 1), (5, 2), (97, 1), (3996169964856590392129, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_97, prime_lucas_3996169964856590392129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825651 : Nat.totient 19381424329554463401825651 = 12128290764811876798354944 := by
  rw [← show ((([(3, 1), (17, 1), (373, 1), (1018841630108524596637, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_17, prime_t59_373, prime_lucas_1018841630108524596637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825652 : Nat.totient 19381424329554463401825652 = 8945246577794274178731648 := by
  rw [← show ((([(2, 2), (13, 1), (341557, 1), (1091237183384554093, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_13, prime_t59_341557, prime_lucas_1091237183384554093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825653 : Nat.totient 19381424329554463401825653 = 19015737077989358226494208 := by
  rw [← show ((([(53, 1), (498107346889, 1), (734153498809, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_53, prime_lucas_498107346889, prime_lucas_734153498809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825654 : Nat.totient 19381424329554463401825654 = 6460474776518154467275164 := by
  rw [← show ((([(2, 1), (3, 4), (119638421787373230875467, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_lucas_119638421787373230875467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825655 : Nat.totient 19381424329554463401825655 = 14045782811897858302771200 := by
  rw [← show ((([(5, 1), (11, 1), (317, 1), (2657, 1), (314761, 1), (1329202861069, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_11, prime_t59_317, prime_t59_2657, prime_t59_314761, prime_lucas_1329202861069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825656 : Nat.totient 19381424329554463401825656 = 8306314440424681534369920 := by
  rw [← show ((([(2, 3), (7, 1), (856391, 1), (14503187, 1), (27865197253, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_7, prime_t59_856391, prime_t59_14503187, prime_lucas_27865197253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825657 : Nat.totient 19381424329554463401825657 = 12230270169407336811866112 := by
  rw [← show ((([(3, 1), (19, 1), (1153, 1), (952363, 1), (309655652837059, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_19, prime_t59_1153, prime_t59_952363, prime_lucas_309655652837059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825658 : Nat.totient 19381424329554463401825658 = 9224587259455319267376000 := by
  rw [← show ((([(2, 1), (29, 1), (71, 1), (51241, 1), (91850547836664191, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_29, prime_t59_71, prime_t59_51241, prime_lucas_91850547836664191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825659 : Nat.totient 19381424329554463401825659 = 19016302983208314126912000 := by
  rw [← show ((([(59, 1), (601, 1), (3911, 1), (333209, 1), (419425341799, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_59, prime_t59_601, prime_t59_3911, prime_t59_333209, prime_lucas_419425341799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825660 : Nat.totient 19381424329554463401825660 = 5133690930011136317664000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (149, 1), (2886839, 1), (750975220952251, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_5, prime_t59_149, prime_t59_2886839, prime_lucas_750975220952251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825661 : Nat.totient 19381424329554463401825661 = 19348714681285799118516480 := by
  rw [← show ((([(643, 1), (7541, 1), (14641873, 1), (272991509939, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_643, prime_t59_7541, prime_t59_14641873, prime_lucas_272991509939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825662 : Nat.totient 19381424329554463401825662 = 9175910174796016668556800 := by
  rw [← show ((([(2, 1), (31, 1), (73, 1), (131, 1), (2939, 1), (11122444788201193, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_31, prime_t59_73, prime_t59_131, prime_t59_2939, prime_lucas_11122444788201193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825663 : Nat.totient 19381424329554463401825663 = 11072585882923857816256512 := by
  rw [← show ((([(3, 2), (7, 1), (4409, 1), (6138113, 1), (11367636094153, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_7, prime_t59_4409, prime_t59_6138113, prime_lucas_11367636094153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825664 : Nat.totient 19381424329554463401825664 = 9581827758431420108762112 := by
  rw [← show ((([(2, 7), (89, 1), (1701318849153306127267, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_89, prime_lucas_1701318849153306127267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825665 : Nat.totient 19381424329554463401825665 = 14231090037098736270627840 := by
  rw [← show ((([(5, 1), (13, 1), (199, 1), (1511, 1), (474083237, 1), (2091703837, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_13, prime_t59_199, prime_t59_1511, prime_lucas_474083237, prime_lucas_2091703837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825666 : Nat.totient 19381424329554463401825666 = 5861389030253308297764480 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (499, 1), (53499352229402229809, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_11, prime_t59_499, prime_lucas_53499352229402229809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825667 : Nat.totient 19381424329554463401825667 = 19378253783600417989213440 := by
  rw [← show ((([(6113, 1), (962679941, 1), (3293437084999, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_6113, prime_lucas_962679941, prime_lucas_3293437084999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825668 : Nat.totient 19381424329554463401825668 = 9066955805444460152401920 := by
  rw [← show ((([(2, 2), (17, 1), (181, 1), (2729, 1), (25248323, 1), (22853995063, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_17, prime_t59_181, prime_t59_2729, prime_t59_25248323, prime_lucas_22853995063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825669 : Nat.totient 19381424329554463401825669 = 12359167591009258841976000 := by
  rw [← show ((([(3, 1), (23, 1), (9483251, 1), (56185543, 1), (527174957, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_23, prime_t59_9483251, prime_lucas_56185543, prime_lucas_527174957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825670 : Nat.totient 19381424329554463401825670 = 6644901821432663356360800 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (42071, 1), (6581195845646802311, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_7, prime_t59_42071, prime_lucas_6581195845646802311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825671 : Nat.totient 19381424329554463401825671 = 19381424329554463401825670 := by
  rw [← show ((([(19381424329554463401825671, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_19381424329554463401825671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825672 : Nat.totient 19381424329554463401825672 = 6458715866968326491563008 := by
  rw [← show ((([(2, 3), (3, 2), (3673, 1), (73287897909498984337, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_3673, prime_lucas_73287897909498984337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825673 : Nat.totient 19381424329554463401825673 = 19374554445584294514140800 := by
  rw [← show ((([(2963, 1), (58997, 1), (60566201, 1), (1830601343, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2963, prime_t59_58997, prime_lucas_60566201, prime_lucas_1830601343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825674 : Nat.totient 19381424329554463401825674 = 9428690520028407511401408 := by
  rw [← show ((([(2, 1), (37, 1), (85447, 1), (59599717, 1), (51429577099, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_37, prime_t59_85447, prime_lucas_59599717, prime_lucas_51429577099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825675 : Nat.totient 19381424329554463401825675 = 10335700188395230742764800 := by
  rw [← show ((([(3, 1), (5, 2), (9767, 1), (9237737, 1), (2864162439871, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_5, prime_t59_9767, prime_t59_9237737, prime_lucas_2864162439871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825676 : Nat.totient 19381424329554463401825676 = 9072713843238278260800000 := by
  rw [← show ((([(2, 2), (19, 1), (103, 1), (1151, 1), (1307, 1), (2281, 1), (721537116451, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_19, prime_t59_103, prime_t59_1151, prime_t59_1307, prime_t59_2281, prime_lucas_721537116451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825677 : Nat.totient 19381424329554463401825677 = 15100119969515858184232320 := by
  rw [← show ((([(7, 1), (11, 1), (6599, 1), (1957333193, 1), (19487318143, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_7, prime_t59_11, prime_t59_6599, prime_lucas_1957333193, prime_lucas_19487318143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825678 : Nat.totient 19381424329554463401825678 = 5920400612536006123837440 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (139, 1), (27983, 1), (4914039716240321, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_13, prime_t59_139, prime_t59_27983, prime_lucas_4914039716240321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825679 : Nat.totient 19381424329554463401825679 = 19350708918572602128605040 := by
  rw [← show ((([(631, 1), (30715410981861273220009, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_631, prime_lucas_30715410981861273220009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825680 : Nat.totient 19381424329554463401825680 = 7752524678282405602490880 := by
  rw [← show ((([(2, 4), (5, 1), (172259, 1), (163810411, 1), (8585632229, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_5, prime_t59_172259, prime_lucas_163810411, prime_lucas_8585632229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825681 : Nat.totient 19381424329554463401825681 = 12909855287533165904936448 := by
  rw [← show ((([(3, 3), (1613, 1), (4259, 1), (249037, 1), (419581220857, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_1613, prime_t59_4259, prime_t59_249037, prime_lucas_419581220857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825682 : Nat.totient 19381424329554463401825682 = 9454353331150443547566880 := by
  rw [← show ((([(2, 1), (41, 1), (27936651683, 1), (8460528339947, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_41, prime_lucas_27936651683, prime_lucas_8460528339947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825683 : Nat.totient 19381424329554463401825683 = 19085465258240987591425440 := by
  rw [← show ((([(67, 1), (4591, 1), (8867, 1), (51199, 1), (138792311083, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_67, prime_t59_4591, prime_t59_8867, prime_t59_51199, prime_lucas_138792311083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825684 : Nat.totient 19381424329554463401825684 = 5537549808444132400521600 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (230731242018505516688401, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_3, prime_t59_7, prime_lucas_230731242018505516688401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825685 : Nat.totient 19381424329554463401825685 = 14587916025237019640448000 := by
  rw [← show ((([(5, 1), (17, 1), (2887, 1), (143501, 1), (550383052859603, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_5, prime_t59_17, prime_t59_2887, prime_t59_143501, prime_lucas_550383052859603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825686 : Nat.totient 19381424329554463401825686 = 9464847512114346944457768 := by
  rw [← show ((([(2, 1), (43, 1), (18959, 1), (11886987667116717839, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_43, prime_t59_18959, prime_lucas_11886987667116717839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825687 : Nat.totient 19381424329554463401825687 = 12469625949242485440184320 := by
  rw [← show ((([(3, 1), (29, 1), (2161, 1), (19364897, 1), (5323490447153, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_3, prime_t59_29, prime_t59_2161, prime_t59_19364897, prime_lucas_5323490447153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t59_19381424329554463401825688 : Nat.totient 19381424329554463401825688 = 8808649230573309431900160 := by
  rw [← show ((([(2, 3), (11, 1), (8089, 1), (27227526058893760609, 1)] : List FactorBlock).map factorBlockValue).prod) = 19381424329554463401825688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t59_2, prime_t59_11, prime_t59_8089, prime_lucas_27227526058893760609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twenty-sixth finite diagonal certificate -/

theorem certifiedKill_diagonal_t59 :
    certifiedKill (periodLcm 59) (periodLcm 59) 88 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t59_9690712164777231700912801, phi_t59_9690712164777231700912802, phi_t59_9690712164777231700912803, phi_t59_9690712164777231700912804, phi_t59_9690712164777231700912805, phi_t59_9690712164777231700912806, phi_t59_9690712164777231700912807, phi_t59_9690712164777231700912808, phi_t59_9690712164777231700912809, phi_t59_9690712164777231700912810, phi_t59_9690712164777231700912811, phi_t59_9690712164777231700912812, phi_t59_9690712164777231700912813, phi_t59_9690712164777231700912814, phi_t59_9690712164777231700912815, phi_t59_9690712164777231700912816, phi_t59_9690712164777231700912817, phi_t59_9690712164777231700912818, phi_t59_9690712164777231700912819, phi_t59_9690712164777231700912820, phi_t59_9690712164777231700912821, phi_t59_9690712164777231700912822, phi_t59_9690712164777231700912823, phi_t59_9690712164777231700912824, phi_t59_9690712164777231700912825, phi_t59_9690712164777231700912826, phi_t59_9690712164777231700912827, phi_t59_9690712164777231700912828, phi_t59_9690712164777231700912829, phi_t59_9690712164777231700912830, phi_t59_9690712164777231700912831, phi_t59_9690712164777231700912832, phi_t59_9690712164777231700912833, phi_t59_9690712164777231700912834, phi_t59_9690712164777231700912835, phi_t59_9690712164777231700912836, phi_t59_9690712164777231700912837, phi_t59_9690712164777231700912838, phi_t59_9690712164777231700912839, phi_t59_9690712164777231700912840, phi_t59_9690712164777231700912841, phi_t59_9690712164777231700912842, phi_t59_9690712164777231700912843, phi_t59_9690712164777231700912844, phi_t59_9690712164777231700912845, phi_t59_9690712164777231700912846, phi_t59_9690712164777231700912847, phi_t59_9690712164777231700912848, phi_t59_9690712164777231700912849, phi_t59_9690712164777231700912850, phi_t59_9690712164777231700912851, phi_t59_9690712164777231700912852, phi_t59_9690712164777231700912853, phi_t59_9690712164777231700912854, phi_t59_9690712164777231700912855, phi_t59_9690712164777231700912856, phi_t59_9690712164777231700912857, phi_t59_9690712164777231700912858, phi_t59_9690712164777231700912859, phi_t59_9690712164777231700912860, phi_t59_9690712164777231700912861, phi_t59_9690712164777231700912862, phi_t59_9690712164777231700912863, phi_t59_9690712164777231700912864, phi_t59_9690712164777231700912865, phi_t59_9690712164777231700912866, phi_t59_9690712164777231700912867, phi_t59_9690712164777231700912868, phi_t59_9690712164777231700912869, phi_t59_9690712164777231700912870, phi_t59_9690712164777231700912871, phi_t59_9690712164777231700912872, phi_t59_9690712164777231700912873, phi_t59_9690712164777231700912874, phi_t59_9690712164777231700912875, phi_t59_9690712164777231700912876, phi_t59_9690712164777231700912877, phi_t59_9690712164777231700912878, phi_t59_9690712164777231700912879, phi_t59_9690712164777231700912880, phi_t59_9690712164777231700912881, phi_t59_9690712164777231700912882, phi_t59_9690712164777231700912883, phi_t59_9690712164777231700912884, phi_t59_9690712164777231700912885, phi_t59_9690712164777231700912886, phi_t59_9690712164777231700912887, phi_t59_9690712164777231700912888, phi_t59_19381424329554463401825601, phi_t59_19381424329554463401825602, phi_t59_19381424329554463401825603, phi_t59_19381424329554463401825604, phi_t59_19381424329554463401825605, phi_t59_19381424329554463401825606, phi_t59_19381424329554463401825607, phi_t59_19381424329554463401825608, phi_t59_19381424329554463401825609, phi_t59_19381424329554463401825610, phi_t59_19381424329554463401825611, phi_t59_19381424329554463401825612, phi_t59_19381424329554463401825613, phi_t59_19381424329554463401825614, phi_t59_19381424329554463401825615, phi_t59_19381424329554463401825616, phi_t59_19381424329554463401825617, phi_t59_19381424329554463401825618, phi_t59_19381424329554463401825619, phi_t59_19381424329554463401825620, phi_t59_19381424329554463401825621, phi_t59_19381424329554463401825622, phi_t59_19381424329554463401825623, phi_t59_19381424329554463401825624, phi_t59_19381424329554463401825625, phi_t59_19381424329554463401825626, phi_t59_19381424329554463401825627, phi_t59_19381424329554463401825628, phi_t59_19381424329554463401825629, phi_t59_19381424329554463401825630, phi_t59_19381424329554463401825631, phi_t59_19381424329554463401825632, phi_t59_19381424329554463401825633, phi_t59_19381424329554463401825634, phi_t59_19381424329554463401825635, phi_t59_19381424329554463401825636, phi_t59_19381424329554463401825637, phi_t59_19381424329554463401825638, phi_t59_19381424329554463401825639, phi_t59_19381424329554463401825640, phi_t59_19381424329554463401825641, phi_t59_19381424329554463401825642, phi_t59_19381424329554463401825643, phi_t59_19381424329554463401825644, phi_t59_19381424329554463401825645, phi_t59_19381424329554463401825646, phi_t59_19381424329554463401825647, phi_t59_19381424329554463401825648, phi_t59_19381424329554463401825649, phi_t59_19381424329554463401825650, phi_t59_19381424329554463401825651, phi_t59_19381424329554463401825652, phi_t59_19381424329554463401825653, phi_t59_19381424329554463401825654, phi_t59_19381424329554463401825655, phi_t59_19381424329554463401825656, phi_t59_19381424329554463401825657, phi_t59_19381424329554463401825658, phi_t59_19381424329554463401825659, phi_t59_19381424329554463401825660, phi_t59_19381424329554463401825661, phi_t59_19381424329554463401825662, phi_t59_19381424329554463401825663, phi_t59_19381424329554463401825664, phi_t59_19381424329554463401825665, phi_t59_19381424329554463401825666, phi_t59_19381424329554463401825667, phi_t59_19381424329554463401825668, phi_t59_19381424329554463401825669, phi_t59_19381424329554463401825670, phi_t59_19381424329554463401825671, phi_t59_19381424329554463401825672, phi_t59_19381424329554463401825673, phi_t59_19381424329554463401825674, phi_t59_19381424329554463401825675, phi_t59_19381424329554463401825676, phi_t59_19381424329554463401825677, phi_t59_19381424329554463401825678, phi_t59_19381424329554463401825679, phi_t59_19381424329554463401825680, phi_t59_19381424329554463401825681, phi_t59_19381424329554463401825682, phi_t59_19381424329554463401825683, phi_t59_19381424329554463401825684, phi_t59_19381424329554463401825685, phi_t59_19381424329554463401825686, phi_t59_19381424329554463401825687, phi_t59_19381424329554463401825688]

def diagonalPincerCertificateScalesThroughT59 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59]

def diagonalPincerKillDepthThroughT59 : ℕ → ℕ
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
  | 53 => 81
  | 59 => 88
  | _ => 0

/-- All 26 imported scales through t=59 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t59 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT59,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT59 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT59, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t37
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t41
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t43
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t47
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t49
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t53
  · simpa [diagonalPincerKillDepthThroughT59] using certifiedKill_diagonal_t59

#print axioms certifiedKill_diagonal_all_imported_through_t59

end TotientTailPeriodKiller
end Erdos249257
