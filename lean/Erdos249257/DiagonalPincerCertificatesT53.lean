import Erdos249257.DiagonalPincerCertificatesT49
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64

/-!
# The t=53 diagonal-pincer certificate

This generated extension consumes 143 new large-prime Lucas roots
and 1099 recursive Pratt dependencies, reuses 0 earlier certificates,
reconstructs all 162 Euler totients in the t=53 window, and proves the
twenty-fifth finite diagonal kill without `native_decide`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=53 window -/

private theorem prime_t53_2 : Nat.Prime 2 := by norm_num
private theorem prime_t53_3 : Nat.Prime 3 := by norm_num
private theorem prime_t53_5 : Nat.Prime 5 := by norm_num
private theorem prime_t53_7 : Nat.Prime 7 := by norm_num
private theorem prime_t53_11 : Nat.Prime 11 := by norm_num
private theorem prime_t53_13 : Nat.Prime 13 := by norm_num
private theorem prime_t53_17 : Nat.Prime 17 := by norm_num
private theorem prime_t53_19 : Nat.Prime 19 := by norm_num
private theorem prime_t53_23 : Nat.Prime 23 := by norm_num
private theorem prime_t53_29 : Nat.Prime 29 := by norm_num
private theorem prime_t53_31 : Nat.Prime 31 := by norm_num
private theorem prime_t53_37 : Nat.Prime 37 := by norm_num
private theorem prime_t53_41 : Nat.Prime 41 := by norm_num
private theorem prime_t53_43 : Nat.Prime 43 := by norm_num
private theorem prime_t53_47 : Nat.Prime 47 := by norm_num
private theorem prime_t53_53 : Nat.Prime 53 := by norm_num
private theorem prime_t53_59 : Nat.Prime 59 := by norm_num
private theorem prime_t53_61 : Nat.Prime 61 := by norm_num
private theorem prime_t53_67 : Nat.Prime 67 := by norm_num
private theorem prime_t53_71 : Nat.Prime 71 := by norm_num
private theorem prime_t53_73 : Nat.Prime 73 := by norm_num
private theorem prime_t53_79 : Nat.Prime 79 := by norm_num
private theorem prime_t53_83 : Nat.Prime 83 := by norm_num
private theorem prime_t53_89 : Nat.Prime 89 := by norm_num
private theorem prime_t53_97 : Nat.Prime 97 := by norm_num
private theorem prime_t53_101 : Nat.Prime 101 := by norm_num
private theorem prime_t53_103 : Nat.Prime 103 := by norm_num
private theorem prime_t53_107 : Nat.Prime 107 := by norm_num
private theorem prime_t53_109 : Nat.Prime 109 := by norm_num
private theorem prime_t53_127 : Nat.Prime 127 := by norm_num
private theorem prime_t53_131 : Nat.Prime 131 := by norm_num
private theorem prime_t53_137 : Nat.Prime 137 := by norm_num
private theorem prime_t53_139 : Nat.Prime 139 := by norm_num
private theorem prime_t53_149 : Nat.Prime 149 := by norm_num
private theorem prime_t53_163 : Nat.Prime 163 := by norm_num
private theorem prime_t53_167 : Nat.Prime 167 := by norm_num
private theorem prime_t53_173 : Nat.Prime 173 := by norm_num
private theorem prime_t53_181 : Nat.Prime 181 := by norm_num
private theorem prime_t53_193 : Nat.Prime 193 := by norm_num
private theorem prime_t53_197 : Nat.Prime 197 := by norm_num
private theorem prime_t53_211 : Nat.Prime 211 := by norm_num
private theorem prime_t53_223 : Nat.Prime 223 := by norm_num
private theorem prime_t53_229 : Nat.Prime 229 := by norm_num
private theorem prime_t53_239 : Nat.Prime 239 := by norm_num
private theorem prime_t53_241 : Nat.Prime 241 := by norm_num
private theorem prime_t53_269 : Nat.Prime 269 := by norm_num
private theorem prime_t53_277 : Nat.Prime 277 := by norm_num
private theorem prime_t53_283 : Nat.Prime 283 := by norm_num
private theorem prime_t53_307 : Nat.Prime 307 := by norm_num
private theorem prime_t53_311 : Nat.Prime 311 := by norm_num
private theorem prime_t53_313 : Nat.Prime 313 := by norm_num
private theorem prime_t53_317 : Nat.Prime 317 := by norm_num
private theorem prime_t53_353 : Nat.Prime 353 := by norm_num
private theorem prime_t53_359 : Nat.Prime 359 := by norm_num
private theorem prime_t53_367 : Nat.Prime 367 := by norm_num
private theorem prime_t53_401 : Nat.Prime 401 := by norm_num
private theorem prime_t53_449 : Nat.Prime 449 := by norm_num
private theorem prime_t53_461 : Nat.Prime 461 := by norm_num
private theorem prime_t53_487 : Nat.Prime 487 := by norm_num
private theorem prime_t53_569 : Nat.Prime 569 := by norm_num
private theorem prime_t53_593 : Nat.Prime 593 := by norm_num
private theorem prime_t53_601 : Nat.Prime 601 := by norm_num
private theorem prime_t53_709 : Nat.Prime 709 := by norm_num
private theorem prime_t53_739 : Nat.Prime 739 := by norm_num
private theorem prime_t53_829 : Nat.Prime 829 := by norm_num
private theorem prime_t53_857 : Nat.Prime 857 := by norm_num
private theorem prime_t53_883 : Nat.Prime 883 := by norm_num
private theorem prime_t53_997 : Nat.Prime 997 := by norm_num
private theorem prime_t53_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_t53_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_t53_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_t53_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_t53_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_t53_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_t53_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_t53_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_t53_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_t53_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_t53_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_t53_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_t53_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_t53_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_t53_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_t53_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_t53_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_t53_2659 : Nat.Prime 2659 := by norm_num
private theorem prime_t53_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_t53_2797 : Nat.Prime 2797 := by norm_num
private theorem prime_t53_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_t53_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_t53_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_t53_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_t53_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_t53_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_t53_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_t53_4463 : Nat.Prime 4463 := by norm_num
private theorem prime_t53_4643 : Nat.Prime 4643 := by norm_num
private theorem prime_t53_5039 : Nat.Prime 5039 := by norm_num
private theorem prime_t53_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_t53_5227 : Nat.Prime 5227 := by norm_num
private theorem prime_t53_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_t53_5639 : Nat.Prime 5639 := by norm_num
private theorem prime_t53_5717 : Nat.Prime 5717 := by norm_num
private theorem prime_t53_6007 : Nat.Prime 6007 := by norm_num
private theorem prime_t53_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_t53_7213 : Nat.Prime 7213 := by norm_num
private theorem prime_t53_7321 : Nat.Prime 7321 := by norm_num
private theorem prime_t53_7649 : Nat.Prime 7649 := by norm_num
private theorem prime_t53_8161 : Nat.Prime 8161 := by norm_num
private theorem prime_t53_10093 : Nat.Prime 10093 := by norm_num
private theorem prime_t53_12241 : Nat.Prime 12241 := by norm_num
private theorem prime_t53_12671 : Nat.Prime 12671 := by norm_num
private theorem prime_t53_12919 : Nat.Prime 12919 := by norm_num
private theorem prime_t53_13693 : Nat.Prime 13693 := by norm_num
private theorem prime_t53_14207 : Nat.Prime 14207 := by norm_num
private theorem prime_t53_14327 : Nat.Prime 14327 := by norm_num
private theorem prime_t53_21017 : Nat.Prime 21017 := by norm_num
private theorem prime_t53_22153 : Nat.Prime 22153 := by norm_num
private theorem prime_t53_25243 : Nat.Prime 25243 := by norm_num
private theorem prime_t53_34843 : Nat.Prime 34843 := by norm_num
private theorem prime_t53_37633 : Nat.Prime 37633 := by norm_num
private theorem prime_t53_37813 : Nat.Prime 37813 := by norm_num
private theorem prime_t53_39821 : Nat.Prime 39821 := by norm_num
private theorem prime_t53_41183 : Nat.Prime 41183 := by norm_num
private theorem prime_t53_41761 : Nat.Prime 41761 := by norm_num
private theorem prime_t53_42467 : Nat.Prime 42467 := by norm_num
private theorem prime_t53_48371 : Nat.Prime 48371 := by norm_num
private theorem prime_t53_61153 : Nat.Prime 61153 := by norm_num
private theorem prime_t53_64879 : Nat.Prime 64879 := by norm_num
private theorem prime_t53_70853 : Nat.Prime 70853 := by norm_num
private theorem prime_t53_71647 : Nat.Prime 71647 := by norm_num
private theorem prime_t53_73999 : Nat.Prime 73999 := by norm_num
private theorem prime_t53_87427 : Nat.Prime 87427 := by norm_num
private theorem prime_t53_126127 : Nat.Prime 126127 := by norm_num
private theorem prime_t53_132749 : Nat.Prime 132749 := by norm_num
private theorem prime_t53_147299 : Nat.Prime 147299 := by norm_num
private theorem prime_t53_157037 : Nat.Prime 157037 := by norm_num
private theorem prime_t53_194093 : Nat.Prime 194093 := by norm_num
private theorem prime_t53_195443 : Nat.Prime 195443 := by norm_num
private theorem prime_t53_202031 : Nat.Prime 202031 := by norm_num
private theorem prime_t53_206651 : Nat.Prime 206651 := by norm_num
private theorem prime_t53_253109 : Nat.Prime 253109 := by norm_num
private theorem prime_t53_260009 : Nat.Prime 260009 := by norm_num
private theorem prime_t53_305621 : Nat.Prime 305621 := by norm_num
private theorem prime_t53_333209 : Nat.Prime 333209 := by norm_num
private theorem prime_t53_408173 : Nat.Prime 408173 := by norm_num
private theorem prime_t53_481249 : Nat.Prime 481249 := by norm_num
private theorem prime_t53_534661 : Nat.Prime 534661 := by norm_num
private theorem prime_t53_593029 : Nat.Prime 593029 := by norm_num
private theorem prime_t53_702391 : Nat.Prime 702391 := by norm_num
private theorem prime_t53_766091 : Nat.Prime 766091 := by norm_num
private theorem prime_t53_857267 : Nat.Prime 857267 := by norm_num
private theorem prime_t53_878821 : Nat.Prime 878821 := by norm_num
private theorem prime_t53_896191 : Nat.Prime 896191 := by norm_num
private theorem prime_t53_1006513 : Nat.Prime 1006513 := by norm_num
private theorem prime_t53_1236811 : Nat.Prime 1236811 := by norm_num
private theorem prime_t53_1282681 : Nat.Prime 1282681 := by norm_num
private theorem prime_t53_1317397 : Nat.Prime 1317397 := by norm_num
private theorem prime_t53_2051947 : Nat.Prime 2051947 := by norm_num
private theorem prime_t53_2074481 : Nat.Prime 2074481 := by norm_num
private theorem prime_t53_2333999 : Nat.Prime 2333999 := by norm_num
private theorem prime_t53_2690137 : Nat.Prime 2690137 := by norm_num
private theorem prime_t53_4962619 : Nat.Prime 4962619 := by norm_num
private theorem prime_t53_5379251 : Nat.Prime 5379251 := by norm_num
private theorem prime_t53_5920169 : Nat.Prime 5920169 := by norm_num
private theorem prime_t53_7339609 : Nat.Prime 7339609 := by norm_num
private theorem prime_t53_7947409 : Nat.Prime 7947409 := by norm_num
private theorem prime_t53_8249599 : Nat.Prime 8249599 := by norm_num
private theorem prime_t53_10195093 : Nat.Prime 10195093 := by norm_num
private theorem prime_t53_11263103 : Nat.Prime 11263103 := by norm_num
private theorem prime_t53_12341669 : Nat.Prime 12341669 := by norm_num
private theorem prime_t53_12469861 : Nat.Prime 12469861 := by norm_num
private theorem prime_t53_13778623 : Nat.Prime 13778623 := by norm_num
private theorem prime_t53_14277931 : Nat.Prime 14277931 := by norm_num
private theorem prime_t53_15877079 : Nat.Prime 15877079 := by norm_num
private theorem prime_t53_20648113 : Nat.Prime 20648113 := by norm_num

/-! ## Exact t=53 window totients -/

private theorem phi_t53_164249358725037825439201 : Nat.totient 164249358725037825439201 = 164217584823835454252880 := by
  rw [← show ((([(5171, 1), (15877079, 1), (2000592052189, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5171, prime_t53_15877079, prime_lucas_2000592052189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439202 : Nat.totient 164249358725037825439202 = 81762576268895898362880 := by
  rw [← show ((([(2, 1), (241, 1), (3833, 1), (88903288392588617, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_241, prime_t53_3833, prime_lucas_88903288392588617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439203 : Nat.totient 164249358725037825439203 = 107926654924261532805120 := by
  rw [← show ((([(3, 1), (73, 1), (1481, 1), (506412607565040977, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_73, prime_t53_1481, prime_lucas_506412607565040977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439204 : Nat.totient 164249358725037825439204 = 82124679229710551830304 := by
  rw [← show ((([(2, 2), (618375557, 1), (66403562069093, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_lucas_618375557, prime_lucas_66403562069093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439205 : Nat.totient 164249358725037825439205 = 131071807461376818304000 := by
  rw [← show ((([(5, 1), (401, 1), (81919879663360511441, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_401, prime_lucas_81919879663360511441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439206 : Nat.totient 164249358725037825439206 = 54748338332593995424224 := by
  rw [← show ((([(2, 1), (3, 1), (37813, 1), (723954542639823277, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_37813, prime_lucas_723954542639823277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439207 : Nat.totient 164249358725037825439207 = 139333759998105340062720 := by
  rw [← show ((([(7, 1), (97, 1), (12469861, 1), (19398685220653, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_7, prime_t53_97, prime_t53_12469861, prime_lucas_19398685220653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439208 : Nat.totient 164249358725037825439208 = 80762342507790761780160 := by
  rw [← show ((([(2, 3), (61, 1), (5039, 1), (66794315293594319, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_61, prime_t53_5039, prime_lucas_66794315293594319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439209 : Nat.totient 164249358725037825439209 = 109435944005805635124480 := by
  rw [← show ((([(3, 2), (1721, 1), (37393229, 1), (283587662989, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_1721, prime_lucas_37393229, prime_lucas_283587662989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439210 : Nat.totient 164249358725037825439210 = 65699743490015130175680 := by
  rw [← show ((([(2, 1), (5, 1), (16424935872503782543921, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_lucas_16424935872503782543921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439211 : Nat.totient 164249358725037825439211 = 149296897662676328913120 := by
  rw [← show ((([(11, 1), (7213, 1), (2070117826714868677, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_11, prime_t53_7213, prime_lucas_2070117826714868677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439212 : Nat.totient 164249358725037825439212 = 54498739212556133941248 := by
  rw [← show ((([(2, 2), (3, 1), (353, 1), (569, 1), (68145230489451793, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_353, prime_t53_569, prime_lucas_68145230489451793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439213 : Nat.totient 164249358725037825439213 = 151614792669265685020800 := by
  rw [← show ((([(13, 1), (12634566055772140418401, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_13, prime_lucas_12634566055772140418401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439214 : Nat.totient 164249358725037825439214 = 70359748565556631564800 := by
  rw [← show ((([(2, 1), (7, 1), (2287, 1), (34843, 1), (2074481, 1), (70971581, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_7, prime_t53_2287, prime_t53_34843, prime_t53_2074481, prime_lucas_70971581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439215 : Nat.totient 164249358725037825439215 = 87283413278684932592640 := by
  rw [← show ((([(3, 1), (5, 1), (277, 1), (191865941, 1), (206032041833, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_5, prime_t53_277, prime_lucas_191865941, prime_lucas_206032041833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439216 : Nat.totient 164249358725037825439216 = 82124679362518912719600 := by
  rw [← show ((([(2, 4), (10265584920314864089951, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_lucas_10265584920314864089951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439217 : Nat.totient 164249358725037825439217 = 154587631741212071001600 := by
  rw [← show ((([(17, 1), (9661726983825754437601, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_17, prime_lucas_9661726983825754437601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439218 : Nat.totient 164249358725037825439218 = 54749743557811461129600 := by
  rw [← show ((([(2, 1), (3, 2), (1282681, 1), (7113977967720121, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_1282681, prime_lucas_7113977967720121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439219 : Nat.totient 164249358725037825439219 = 155604148591970011088160 := by
  rw [← show ((([(19, 1), (408173, 1), (1236811, 1), (17123891567, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_19, prime_t53_408173, prime_t53_1236811, prime_lucas_17123891567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439220 : Nat.totient 164249358725037825439220 = 65663861531722437329280 := by
  rw [← show ((([(2, 2), (5, 1), (1831, 1), (1438397203, 1), (3118218277, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_1831, prime_lucas_1438397203, prime_lucas_3118218277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439221 : Nat.totient 164249358725037825439221 = 93554986136447819722800 := by
  rw [← show ((([(3, 1), (7, 1), (311, 1), (25149189821625757991, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_7, prime_t53_311, prime_lucas_25149189821625757991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439222 : Nat.totient 164249358725037825439222 = 74658654477539814780000 := by
  rw [← show ((([(2, 1), (11, 1), (534661, 1), (14277931, 1), (977996311, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_11, prime_t53_534661, prime_t53_14277931, prime_lucas_977996311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439223 : Nat.totient 164249358725037825439223 = 156198880075008508160896 := by
  rw [← show ((([(23, 1), (173, 1), (157037, 1), (2333999, 1), (112622999, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_23, prime_t53_173, prime_t53_157037, prime_t53_2333999, prime_lucas_112622999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439224 : Nat.totient 164249358725037825439224 = 54749786241679275146400 := by
  rw [← show ((([(2, 3), (3, 1), (6843723280209909393301, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_lucas_6843723280209909393301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439225 : Nat.totient 164249358725037825439225 = 131399486980030260351360 := by
  rw [← show ((([(5, 2), (6569974349001513017569, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_lucas_6569974349001513017569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439226 : Nat.totient 164249358725037825439226 = 75737912011686341266800 := by
  rw [← show ((([(2, 1), (13, 1), (1091, 1), (5790360245541769211, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_13, prime_t53_1091, prime_lucas_5790360245541769211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439227 : Nat.totient 164249358725037825439227 = 109419257536785385042464 := by
  rw [← show ((([(3, 3), (2659, 1), (2797, 1), (817954441114487, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_2659, prime_t53_2797, prime_lucas_817954441114487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439228 : Nat.totient 164249358725037825439228 = 70380268909326955998720 := by
  rw [← show ((([(2, 2), (7, 1), (5717, 1), (130539181, 1), (7860253913, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_7, prime_t53_5717, prime_lucas_130539181, prime_lucas_7860253913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439229 : Nat.totient 164249358725037825439229 = 157327411540248790364160 := by
  rw [← show ((([(29, 1), (229, 1), (283, 1), (21017, 1), (702391, 1), (5920169, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_29, prime_t53_229, prime_t53_283, prime_t53_21017, prime_t53_702391, prime_t53_5920169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439230 : Nat.totient 164249358725037825439230 = 43787348453862039237120 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (3511, 1), (7947409, 1), (196212212359, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_5, prime_t53_3511, prime_t53_7947409, prime_lucas_196212212359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439231 : Nat.totient 164249358725037825439231 = 157617824796202932887040 := by
  rw [← show ((([(31, 1), (127, 1), (1933, 1), (124396049, 1), (173500139, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_31, prime_t53_127, prime_t53_1933, prime_lucas_124396049, prime_lucas_173500139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439232 : Nat.totient 164249358725037825439232 = 82056298735456245350400 := by
  rw [← show ((([(2, 9), (1201, 1), (281736173, 1), (948086807, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_1201, prime_lucas_281736173, prime_lucas_948086807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439233 : Nat.totient 164249358725037825439233 = 99523764428429349129600 := by
  rw [← show ((([(3, 1), (11, 1), (7321, 1), (12919, 1), (52624797497599, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_11, prime_t53_7321, prime_t53_12919, prime_lucas_52624797497599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439234 : Nat.totient 164249358725037825439234 = 77293815868319153760000 := by
  rw [← show ((([(2, 1), (17, 1), (54840057901, 1), (88090050901, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_17, prime_lucas_54840057901, prime_lucas_88090050901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439235 : Nat.totient 164249358725037825439235 = 112628131348051845097056 := by
  rw [← show ((([(5, 1), (7, 1), (322615759, 1), (14546216946319, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_7, prime_lucas_322615759, prime_lucas_14546216946319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439236 : Nat.totient 164249358725037825439236 = 54335571615758834069760 := by
  rw [← show ((([(2, 2), (3, 2), (139, 1), (2677, 1), (2051947, 1), (5975467261, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_139, prime_t53_2677, prime_t53_2051947, prime_lucas_5975467261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439237 : Nat.totient 164249358725037825439237 = 159810186867604370696304 := by
  rw [← show ((([(37, 2), (119977617768471749773, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_37, prime_lucas_119977617768471749773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439238 : Nat.totient 164249358725037825439238 = 76483638097598071323360 := by
  rw [← show ((([(2, 1), (19, 1), (59, 1), (12341669, 1), (5936003929831, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_19, prime_t53_59, prime_t53_12341669, prime_lucas_5936003929831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439239 : Nat.totient 164249358725037825439239 = 99642910912141112006400 := by
  rw [← show ((([(3, 1), (13, 1), (71, 2), (10093, 1), (766091, 1), (108049247, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_13, prime_t53_71, prime_t53_10093, prime_t53_766091, prime_lucas_108049247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439240 : Nat.totient 164249358725037825439240 = 65677614913561773735424 := by
  rw [← show ((([(2, 3), (5, 1), (2969, 1), (1383036028334774549, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_2969, prime_lucas_1383036028334774549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439241 : Nat.totient 164249358725037825439241 = 159073617850134550535680 := by
  rw [← show ((([(41, 1), (137, 1), (29241473869510027673, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_41, prime_t53_137, prime_lucas_29241473869510027673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439242 : Nat.totient 164249358725037825439242 = 46927380704956209529344 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (61153, 1), (195443, 1), (327202418219, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_7, prime_t53_61153, prime_t53_195443, prime_lucas_327202418219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439243 : Nat.totient 164249358725037825439243 = 160429606196548573684800 := by
  rw [← show ((([(43, 1), (3819752528489251754401, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_43, prime_lucas_3819752528489251754401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439244 : Nat.totient 164249358725037825439244 = 74657707197147875491200 := by
  rw [← show ((([(2, 2), (11, 1), (73999, 1), (896191, 1), (56289135289, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_11, prime_t53_73999, prime_t53_896191, prime_lucas_56289135289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439245 : Nat.totient 164249358725037825439245 = 87513576220287867500928 := by
  rw [← show ((([(3, 2), (5, 1), (1303, 1), (4643, 1), (603320482189709, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_5, prime_t53_1303, prime_t53_4643, prime_lucas_603320482189709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439246 : Nat.totient 164249358725037825439246 = 78547609236425036400000 := by
  rw [← show ((([(2, 1), (23, 1), (12241, 1), (5379251, 1), (54225946811, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_23, prime_t53_12241, prime_t53_5379251, prime_lucas_54225946811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439247 : Nat.totient 164249358725037825439247 = 160157068613391668440320 := by
  rw [← show ((([(47, 1), (269, 1), (7339609, 1), (1770029971181, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_47, prime_t53_269, prime_t53_7339609, prime_lucas_1770029971181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439248 : Nat.totient 164249358725037825439248 = 54749786241679275146400 := by
  rw [← show ((([(2, 4), (3, 1), (3421861640104954696651, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_lucas_3421861640104954696651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439249 : Nat.totient 164249358725037825439249 = 139391252100456428940000 := by
  rw [← show ((([(7, 2), (101, 1), (33188393357251530701, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_7, prime_t53_101, prime_lucas_33188393357251530701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439250 : Nat.totient 164249358725037825439250 = 65699425563929631990000 := by
  rw [← show ((([(2, 1), (5, 3), (206651, 1), (3179260854775207, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_206651, prime_lucas_3179260854775207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439251 : Nat.totient 164249358725037825439251 = 103055918710254157080704 := by
  rw [← show ((([(3, 1), (17, 1), (41183, 1), (78201579809029247, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_17, prime_t53_41183, prime_lucas_78201579809029247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439252 : Nat.totient 164249358725037825439252 = 75807396326371305194496 := by
  rw [← show ((([(2, 2), (13, 1), (9434520169, 1), (334796201329, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_13, prime_lucas_9434520169, prime_lucas_334796201329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439253 : Nat.totient 164249358725037825439253 = 160822110860407008230400 := by
  rw [← show ((([(53, 1), (593, 1), (2851, 1), (8249599, 1), (222199493, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_53, prime_t53_593, prime_t53_2851, prime_t53_8249599, prime_lucas_222199493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439254 : Nat.totient 164249358725037825439254 = 54749607098929769310480 := by
  rw [← show ((([(2, 1), (3, 4), (305621, 1), (3317458323876527, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_305621, prime_lucas_3317458323876527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439255 : Nat.totient 164249358725037825439255 = 119285596591693068735360 := by
  rw [← show ((([(5, 1), (11, 1), (709, 1), (4212062026542834349, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_11, prime_t53_709, prime_lucas_4212062026542834349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439256 : Nat.totient 164249358725037825439256 = 70387295279283940220928 := by
  rw [← show ((([(2, 3), (7, 1), (13693, 1), (481249, 1), (445089354793, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_7, prime_t53_13693, prime_t53_481249, prime_lucas_445089354793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439257 : Nat.totient 164249358725037825439257 = 103632387263687989670400 := by
  rw [← show ((([(3, 1), (19, 1), (997, 1), (83576201, 1), (34582074533, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_19, prime_t53_997, prime_lucas_83576201, prime_lucas_34582074533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439258 : Nat.totient 164249358725037825439258 = 79276995465603039808704 := by
  rw [← show ((([(2, 1), (29, 1), (5227, 1), (126127, 1), (4295513843869, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_29, prime_t53_5227, prime_t53_126127, prime_lucas_4295513843869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439259 : Nat.totient 164249358725037825439259 = 164249358700348581822240 := by
  rw [← show ((([(6654462289, 1), (24682589154731, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_6654462289, prime_lucas_24682589154731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439260 : Nat.totient 164249358725037825439260 = 42746579519456030736384 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (103, 1), (107, 1), (193, 1), (1286986883770157, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_5, prime_t53_103, prime_t53_107, prime_t53_193, prime_lucas_1286986883770157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439261 : Nat.totient 164249358725037825439261 = 164249358725037825439260 := by
  rw [← show ((([(164249358725037825439261, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_164249358725037825439261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439262 : Nat.totient 164249358725037825439262 = 78119391733823360340000 := by
  rw [← show ((([(2, 1), (31, 1), (83, 1), (197, 1), (162019644379092751, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_31, prime_t53_83, prime_t53_197, prime_lucas_162019644379092751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439263 : Nat.totient 164249358725037825439263 = 93856776414307328822400 := by
  rw [← show ((([(3, 2), (7, 1), (2607132678175203578401, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_7, prime_lucas_2607132678175203578401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439264 : Nat.totient 164249358725037825439264 = 82124679356678451609600 := by
  rw [← show ((([(2, 5), (14649233777, 1), (350379585601, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_lucas_14649233777, prime_lucas_350379585601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439265 : Nat.totient 164249358725037825439265 = 120621116459258649504000 := by
  rw [← show ((([(5, 1), (13, 1), (181, 1), (202031, 1), (69102496500371, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_13, prime_t53_181, prime_t53_202031, prime_lucas_69102496500371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439266 : Nat.totient 164249358725037825439266 = 48579764014394666760960 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (67, 1), (109, 1), (593029, 1), (574622351323, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_11, prime_t53_67, prime_t53_109, prime_t53_593029, prime_lucas_574622351323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439267 : Nat.totient 164249358725037825439267 = 164249358725037825439266 := by
  rw [← show ((([(164249358725037825439267, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_164249358725037825439267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439268 : Nat.totient 164249358725037825439268 = 77293815870606035500800 := by
  rw [← show ((([(2, 2), (17, 1), (2415431745956438609401, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_17, prime_lucas_2415431745956438609401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439269 : Nat.totient 164249358725037825439269 = 103021692964136146200000 := by
  rw [← show ((([(3, 1), (23, 1), (61, 1), (322520591, 1), (120994968251, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_23, prime_t53_61, prime_lucas_322520591, prime_lucas_120994968251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439270 : Nat.totient 164249358725037825439270 = 56134148705298185154048 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (313, 1), (7496547636925505497, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_7, prime_t53_313, prime_lucas_7496547636925505497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439271 : Nat.totient 164249358725037825439271 = 164219804169579167321088 := by
  rw [← show ((([(5569, 1), (2690137, 1), (10963571846207, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5569, prime_t53_2690137, prime_lucas_10963571846207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439272 : Nat.totient 164249358725037825439272 = 54558459147058061475456 := by
  rw [← show ((([(2, 3), (3, 2), (307, 1), (4463, 1), (71647, 1), (23238490463, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_307, prime_t53_4463, prime_t53_71647, prime_lucas_23238490463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439273 : Nat.totient 164249358725037825439273 = 162726734910619095552576 := by
  rw [← show ((([(163, 1), (317, 1), (162144187, 1), (19604484749, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_163, prime_t53_317, prime_lucas_162144187, prime_lucas_19604484749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439274 : Nat.totient 164249358725037825439274 = 79903026172766014986240 := by
  rw [← show ((([(2, 1), (37, 1), (39821, 1), (1317397, 1), (42310010273, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_37, prime_t53_39821, prime_t53_1317397, prime_lucas_42310010273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439275 : Nat.totient 164249358725037825439275 = 87599657963595062730240 := by
  rw [← show ((([(3, 1), (5, 2), (3818804713, 1), (573475632889, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_5, prime_lucas_3818804713, prime_lucas_573475632889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439276 : Nat.totient 164249358725037825439276 = 76649638152912553798272 := by
  rw [← show ((([(2, 2), (19, 1), (73, 1), (883, 1), (33527913444171739, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_19, prime_t53_73, prime_t53_883, prime_lucas_33527913444171739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439277 : Nat.totient 164249358725037825439277 = 127708955671435772889600 := by
  rw [← show ((([(7, 1), (11, 1), (857, 1), (1021, 1), (42467, 1), (57405672799, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_7, prime_t53_11, prime_t53_857, prime_t53_1021, prime_t53_42467, prime_lucas_57405672799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439278 : Nat.totient 164249358725037825439278 = 49898539359505162134432 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (79, 1), (2050400203792947163, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_13, prime_t53_79, prime_lucas_2050400203792947163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439279 : Nat.totient 164249358725037825439279 = 164241614752480713630336 := by
  rw [← show ((([(25243, 1), (132749, 1), (49015276526897, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_25243, prime_t53_132749, prime_lucas_49015276526897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439280 : Nat.totient 164249358725037825439280 = 65619700522261019688960 := by
  rw [← show ((([(2, 4), (5, 1), (1087, 1), (6043, 1), (8161, 1), (147299, 1), (260009, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_1087, prime_t53_6043, prime_t53_8161, prime_t53_147299, prime_t53_260009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_164249358725037825439281 : Nat.totient 164249358725037825439281 = 108712569102228498666816 := by
  rw [← show ((([(3, 3), (167, 1), (829, 1), (4962619, 1), (8854376459, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_167, prime_t53_829, prime_t53_4962619, prime_lucas_8854376459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878401 : Nat.totient 328498717450075650878401 = 327867292813936450464000 := by
  rw [← show ((([(601, 1), (3911, 1), (333209, 1), (419425341799, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_601, prime_t53_3911, prime_t53_333209, prime_lucas_419425341799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878402 : Nat.totient 328498717450075650878402 = 164217584823835454252880 := by
  rw [← show ((([(2, 1), (5171, 1), (15877079, 1), (2000592052189, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5171, prime_t53_15877079, prime_lucas_2000592052189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878403 : Nat.totient 328498717450075650878403 = 218923610786096103408864 := by
  rw [← show ((([(3, 1), (3023, 1), (70853, 1), (511229648870179, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_3023, prime_t53_70853, prime_lucas_511229648870179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878404 : Nat.totient 328498717450075650878404 = 163525152537791796725760 := by
  rw [← show ((([(2, 2), (241, 1), (3833, 1), (88903288392588617, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_241, prime_t53_3833, prime_lucas_88903288392588617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878405 : Nat.totient 328498717450075650878405 = 262764616661856826003456 := by
  rw [← show ((([(5, 1), (7649, 1), (8589324550923667169, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_7649, prime_lucas_8589324550923667169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878406 : Nat.totient 328498717450075650878406 = 107926654924261532805120 := by
  rw [← show ((([(2, 1), (3, 1), (73, 1), (1481, 1), (506412607565040977, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_73, prime_t53_1481, prime_lucas_506412607565040977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878407 : Nat.totient 328498717450075650878407 = 277604274149598907405440 := by
  rw [← show ((([(7, 1), (71, 1), (1006513, 1), (656686216854887, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_7, prime_t53_71, prime_t53_1006513, prime_lucas_656686216854887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878408 : Nat.totient 328498717450075650878408 = 164249358459421103660608 := by
  rw [← show ((([(2, 3), (618375557, 1), (66403562069093, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_lucas_618375557, prime_lucas_66403562069093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878409 : Nat.totient 328498717450075650878409 = 218999144966717100585600 := by
  rw [← show ((([(3, 2), (36499857494452850097601, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_lucas_36499857494452850097601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878410 : Nat.totient 328498717450075650878410 = 131071807461376818304000 := by
  rw [← show ((([(2, 1), (5, 1), (401, 1), (81919879663360511441, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_401, prime_lucas_81919879663360511441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878411 : Nat.totient 328498717450075650878411 = 298635197681886955344000 := by
  rw [← show ((([(11, 1), (29863519768188695534401, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_11, prime_lucas_29863519768188695534401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878412 : Nat.totient 328498717450075650878412 = 109496676665187990848448 := by
  rw [← show ((([(2, 2), (3, 1), (37813, 1), (723954542639823277, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_37813, prime_lucas_723954542639823277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878413 : Nat.totient 328498717450075650878413 = 300392228020352357707776 := by
  rw [← show ((([(13, 1), (107, 1), (87427, 1), (2701226316721409, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_13, prime_t53_107, prime_t53_87427, prime_lucas_2701226316721409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878414 : Nat.totient 328498717450075650878414 = 139333759998105340062720 := by
  rw [← show ((([(2, 1), (7, 1), (97, 1), (12469861, 1), (19398685220653, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_7, prime_t53_97, prime_t53_12469861, prime_lucas_19398685220653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878415 : Nat.totient 328498717450075650878415 = 175199315973373680468480 := by
  rw [← show ((([(3, 1), (5, 1), (21899914496671710058561, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_5, prime_lucas_21899914496671710058561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878416 : Nat.totient 328498717450075650878416 = 161524685015581523560320 := by
  rw [← show ((([(2, 4), (61, 1), (5039, 1), (66794315293594319, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_61, prime_t53_5039, prime_lucas_66794315293594319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878417 : Nat.totient 328498717450075650878417 = 300976181611233276395520 := by
  rw [← show ((([(17, 1), (59, 1), (103, 1), (37633, 1), (84494157535061, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_17, prime_t53_59, prime_t53_103, prime_t53_37633, prime_lucas_84494157535061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878418 : Nat.totient 328498717450075650878418 = 109435944005805635124480 := by
  rw [← show ((([(2, 1), (3, 2), (1721, 1), (37393229, 1), (283587662989, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_1721, prime_lucas_37393229, prime_lucas_283587662989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878419 : Nat.totient 328498717450075650878419 = 311209311268492721884476 := by
  rw [← show ((([(19, 2), (909968746399101525979, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_19, prime_lucas_909968746399101525979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878420 : Nat.totient 328498717450075650878420 = 131399486980030260351360 := by
  rw [← show ((([(2, 2), (5, 1), (16424935872503782543921, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_lucas_16424935872503782543921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878421 : Nat.totient 328498717450075650878421 = 187202071758236961025584 := by
  rw [← show ((([(3, 1), (7, 1), (367, 1), (42623422531474717903, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_7, prime_t53_367, prime_lucas_42623422531474717903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878422 : Nat.totient 328498717450075650878422 = 149296897662676328913120 := by
  rw [← show ((([(2, 1), (11, 1), (7213, 1), (2070117826714868677, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_11, prime_t53_7213, prime_lucas_2070117826714868677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878423 : Nat.totient 328498717450075650878423 = 311203353131409547670400 := by
  rw [← show ((([(23, 1), (109, 1), (2423, 1), (194093, 1), (278622418351, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_23, prime_t53_109, prime_t53_2423, prime_t53_194093, prime_lucas_278622418351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878424 : Nat.totient 328498717450075650878424 = 108997478425112267882496 := by
  rw [← show ((([(2, 3), (3, 1), (353, 1), (569, 1), (68145230489451793, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_353, prime_t53_569, prime_lucas_68145230489451793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878425 : Nat.totient 328498717450075650878425 = 262778233767971493496400 := by
  rw [← show ((([(5, 2), (12671, 1), (1037009604451347647, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_12671, prime_lucas_1037009604451347647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878426 : Nat.totient 328498717450075650878426 = 151614792669265685020800 := by
  rw [← show ((([(2, 1), (13, 1), (12634566055772140418401, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_13, prime_lucas_12634566055772140418401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878427 : Nat.totient 328498717450075650878427 = 218337812617070135808000 := by
  rw [← show ((([(3, 6), (449, 1), (1259, 1), (10195093, 1), (78188501, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_449, prime_t53_1259, prime_t53_10195093, prime_lucas_78188501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878428 : Nat.totient 328498717450075650878428 = 140719497131113263129600 := by
  rw [← show ((([(2, 2), (7, 1), (2287, 1), (34843, 1), (2074481, 1), (70971581, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_7, prime_t53_2287, prime_t53_34843, prime_t53_2074481, prime_lucas_70971581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878429 : Nat.totient 328498717450075650878429 = 317171160108255353435136 := by
  rw [← show ((([(29, 1), (20648113, 1), (548599379567377, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_29, prime_t53_20648113, prime_lucas_548599379567377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878430 : Nat.totient 328498717450075650878430 = 87283413278684932592640 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (277, 1), (191865941, 1), (206032041833, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_5, prime_t53_277, prime_lucas_191865941, prime_lucas_206032041833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878431 : Nat.totient 328498717450075650878431 = 317205834567163975440000 := by
  rw [← show ((([(31, 2), (461, 1), (48371, 1), (15329369738041, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_31, prime_t53_461, prime_t53_48371, prime_lucas_15329369738041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878432 : Nat.totient 328498717450075650878432 = 164249358725037825439200 := by
  rw [← show ((([(2, 5), (10265584920314864089951, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_lucas_10265584920314864089951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878433 : Nat.totient 328498717450075650878433 = 199090131787924636896000 := by
  rw [← show ((([(3, 1), (11, 1), (9954506589396231844801, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_11, prime_lucas_9954506589396231844801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878434 : Nat.totient 328498717450075650878434 = 154587631741212071001600 := by
  rw [← show ((([(2, 1), (17, 1), (9661726983825754437601, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_17, prime_lucas_9661726983825754437601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878435 : Nat.totient 328498717450075650878435 = 225256263306079951047168 := by
  rw [← show ((([(5, 1), (7, 1), (2554031833, 1), (3674847556777, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_7, prime_lucas_2554031833, prime_lucas_3674847556777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878436 : Nat.totient 328498717450075650878436 = 109499487115622922259200 := by
  rw [← show ((([(2, 2), (3, 2), (1282681, 1), (7113977967720121, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_1282681, prime_lucas_7113977967720121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878437 : Nat.totient 328498717450075650878437 = 319453253696836441772928 := by
  rw [← show ((([(37, 1), (2207, 1), (14327, 1), (280785295354009, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_37, prime_t53_2207, prime_t53_14327, prime_lucas_280785295354009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878438 : Nat.totient 328498717450075650878438 = 155604148591970011088160 := by
  rw [← show ((([(2, 1), (19, 1), (408173, 1), (1236811, 1), (17123891567, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_19, prime_t53_408173, prime_t53_1236811, prime_lucas_17123891567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878439 : Nat.totient 328498717450075650878439 = 202153056765662817264768 := by
  rw [← show ((([(3, 1), (13, 1), (1596115853, 1), (5277213443717, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_13, prime_lucas_1596115853, prime_lucas_5277213443717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878440 : Nat.totient 328498717450075650878440 = 131327723063444874658560 := by
  rw [← show ((([(2, 3), (5, 1), (1831, 1), (1438397203, 1), (3118218277, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_1831, prime_lucas_1438397203, prime_lucas_3118218277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878441 : Nat.totient 328498717450075650878441 = 316625269831398217710880 := by
  rw [← show ((([(41, 1), (83, 1), (96532094460792139547, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_41, prime_t53_83, prime_lucas_96532094460792139547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878442 : Nat.totient 328498717450075650878442 = 93554986136447819722800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (311, 1), (25149189821625757991, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_7, prime_t53_311, prime_lucas_25149189821625757991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878443 : Nat.totient 328498717450075650878443 = 320859212393097147369600 := by
  rw [← show ((([(43, 1), (7639505056978503508801, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_43, prime_lucas_7639505056978503508801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878444 : Nat.totient 328498717450075650878444 = 149317308955079629560000 := by
  rw [← show ((([(2, 2), (11, 1), (534661, 1), (14277931, 1), (977996311, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_11, prime_t53_534661, prime_t53_14277931, prime_lucas_977996311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878445 : Nat.totient 328498717450075650878445 = 175199315817098062061568 := by
  rw [← show ((([(3, 2), (5, 1), (1121284897, 1), (6510362815393, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_5, prime_lucas_1121284897, prime_lucas_6510362815393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878446 : Nat.totient 328498717450075650878446 = 156198880075008508160896 := by
  rw [← show ((([(2, 1), (23, 1), (173, 1), (157037, 1), (2333999, 1), (112622999, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_23, prime_t53_173, prime_t53_157037, prime_t53_2333999, prime_lucas_112622999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878447 : Nat.totient 328498717450075650878447 = 321509378240076429343512 := by
  rw [← show ((([(47, 1), (67034683, 1), (104264450893747, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_47, prime_lucas_67034683, prime_lucas_104264450893747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878448 : Nat.totient 328498717450075650878448 = 109499572483358550292800 := by
  rw [← show ((([(2, 4), (3, 1), (6843723280209909393301, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_lucas_6843723280209909393301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878449 : Nat.totient 328498717450075650878449 = 279590962436193492564480 := by
  rw [← show ((([(7, 2), (149, 1), (3121, 1), (13778623, 1), (1046289203, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_7, prime_t53_149, prime_t53_3121, prime_t53_13778623, prime_lucas_1046289203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878450 : Nat.totient 328498717450075650878450 = 131399486980030260351360 := by
  rw [← show ((([(2, 1), (5, 2), (6569974349001513017569, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_lucas_6569974349001513017569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878451 : Nat.totient 328498717450075650878451 = 206116027981381951804928 := by
  rw [← show ((([(3, 1), (17, 1), (253109, 1), (25448132316711389, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_17, prime_t53_253109, prime_lucas_25448132316711389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878452 : Nat.totient 328498717450075650878452 = 151475824023372682533600 := by
  rw [← show ((([(2, 2), (13, 1), (1091, 1), (5790360245541769211, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_13, prime_t53_1091, prime_lucas_5790360245541769211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878453 : Nat.totient 328498717450075650878453 = 322300628413597494086608 := by
  rw [← show ((([(53, 1), (11774005559, 1), (526421444039, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_53, prime_lucas_11774005559, prime_lucas_526421444039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878454 : Nat.totient 328498717450075650878454 = 109419257536785385042464 := by
  rw [← show ((([(2, 1), (3, 3), (2659, 1), (2797, 1), (817954441114487, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_2659, prime_t53_2797, prime_lucas_817954441114487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878455 : Nat.totient 328498717450075650878455 = 238908158145509564275200 := by
  rw [← show ((([(5, 1), (11, 1), (5972703953637739106881, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_11, prime_lucas_5972703953637739106881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878456 : Nat.totient 328498717450075650878456 = 140760537818653911997440 := by
  rw [← show ((([(2, 3), (7, 1), (5717, 1), (130539181, 1), (7860253913, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_7, prime_t53_5717, prime_lucas_130539181, prime_lucas_7860253913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878457 : Nat.totient 328498717450075650878457 = 207046851683958624739968 := by
  rw [← show ((([(3, 1), (19, 1), (487, 1), (1475650079, 1), (8019484937, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_19, prime_t53_487, prime_lucas_1475650079, prime_lucas_8019484937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878458 : Nat.totient 328498717450075650878458 = 157327411540248790364160 := by
  rw [← show ((([(2, 1), (29, 1), (229, 1), (283, 1), (21017, 1), (702391, 1), (5920169, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_29, prime_t53_229, prime_t53_283, prime_t53_21017, prime_t53_702391, prime_t53_5920169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878459 : Nat.totient 328498717450075650878459 = 325665603749944192757760 := by
  rw [← show ((([(223, 1), (359, 1), (739, 1), (41761, 1), (132959397553, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_223, prime_t53_359, prime_t53_739, prime_t53_41761, prime_lucas_132959397553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878460 : Nat.totient 328498717450075650878460 = 87574696907724078474240 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (3511, 1), (7947409, 1), (196212212359, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_5, prime_t53_3511, prime_t53_7947409, prime_lucas_196212212359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878461 : Nat.totient 328498717450075650878461 = 324446111972377864560000 := by
  rw [← show ((([(131, 1), (211, 1), (2700707881, 1), (4400502941, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_131, prime_t53_211, prime_lucas_2700707881, prime_lucas_4400502941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878462 : Nat.totient 328498717450075650878462 = 157617824796202932887040 := by
  rw [← show ((([(2, 1), (31, 1), (127, 1), (1933, 1), (124396049, 1), (173500139, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_31, prime_t53_127, prime_t53_1933, prime_lucas_124396049, prime_lucas_173500139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878463 : Nat.totient 328498717450075650878463 = 187713536162376464183952 := by
  rw [← show ((([(3, 2), (7, 1), (11263103, 1), (462951049666367, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_7, prime_t53_11263103, prime_lucas_462951049666367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878464 : Nat.totient 328498717450075650878464 = 164112597470912490700800 := by
  rw [← show ((([(2, 10), (1201, 1), (281736173, 1), (948086807, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_1201, prime_lucas_281736173, prime_lucas_948086807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878465 : Nat.totient 328498717450075650878465 = 238855152175331360486400 := by
  rw [← show ((([(5, 1), (13, 1), (67, 1), (2221, 1), (878821, 1), (38645286763, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_5, prime_t53_13, prime_t53_67, prime_t53_2221, prime_t53_878821, prime_lucas_38645286763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878466 : Nat.totient 328498717450075650878466 = 99523764428429349129600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (7321, 1), (12919, 1), (52624797497599, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_11, prime_t53_7321, prime_t53_12919, prime_lucas_52624797497599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878467 : Nat.totient 328498717450075650878467 = 328259918448354836596872 := by
  rw [← show ((([(1523, 1), (14207, 1), (15182084157975247, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_1523, prime_t53_14207, prime_lucas_15182084157975247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878468 : Nat.totient 328498717450075650878468 = 154587631736638307520000 := by
  rw [← show ((([(2, 2), (17, 1), (54840057901, 1), (88090050901, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_17, prime_lucas_54840057901, prime_lucas_88090050901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878469 : Nat.totient 328498717450075650878469 = 209319340933455384869952 := by
  rw [← show ((([(3, 1), (23, 1), (1327, 1), (857267, 1), (4185020199989, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_23, prime_t53_1327, prime_t53_857267, prime_lucas_4185020199989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878470 : Nat.totient 328498717450075650878470 = 112628131348051845097056 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (322615759, 1), (14546216946319, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_7, prime_lucas_322615759, prime_lucas_14546216946319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878471 : Nat.totient 328498717450075650878471 = 328498717450075650878470 := by
  rw [← show ((([(328498717450075650878471, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_328498717450075650878471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878472 : Nat.totient 328498717450075650878472 = 108671143231517668139520 := by
  rw [← show ((([(2, 3), (3, 2), (139, 1), (2677, 1), (2051947, 1), (5975467261, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_139, prime_t53_2677, prime_t53_2051947, prime_lucas_5975467261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878473 : Nat.totient 328498717450075650878473 = 328177017710966667260160 := by
  rw [← show ((([(1321, 1), (5639, 1), (22153, 1), (1990656006239, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_1321, prime_t53_5639, prime_t53_22153, prime_lucas_1990656006239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878474 : Nat.totient 328498717450075650878474 = 159810186867604370696304 := by
  rw [← show ((([(2, 1), (37, 2), (119977617768471749773, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_37, prime_lucas_119977617768471749773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878475 : Nat.totient 328498717450075650878475 = 173199276564057943879680 := by
  rw [← show ((([(3, 1), (5, 2), (89, 1), (6007, 1), (64879, 1), (126275945489, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_t53_5, prime_t53_89, prime_t53_6007, prime_t53_64879, prime_lucas_126275945489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878476 : Nat.totient 328498717450075650878476 = 152967276195196142646720 := by
  rw [← show ((([(2, 2), (19, 1), (59, 1), (12341669, 1), (5936003929831, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_19, prime_t53_59, prime_t53_12341669, prime_lucas_5936003929831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878477 : Nat.totient 328498717450075650878477 = 247549575756051288720000 := by
  rw [← show ((([(7, 1), (11, 2), (61, 1), (79, 1), (239, 1), (336740568467551, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_7, prime_t53_11, prime_t53_61, prime_t53_79, prime_t53_239, prime_lucas_336740568467551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878478 : Nat.totient 328498717450075650878478 = 99642910912141112006400 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (71, 2), (10093, 1), (766091, 1), (108049247, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_3, prime_t53_13, prime_t53_71, prime_t53_10093, prime_t53_766091, prime_lucas_108049247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878479 : Nat.totient 328498717450075650878479 = 323998735019252696756784 := by
  rw [← show ((([(73, 1), (4499982430822954121623, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_73, prime_lucas_4499982430822954121623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878480 : Nat.totient 328498717450075650878480 = 131355229827123547470848 := by
  rw [← show ((([(2, 4), (5, 1), (2969, 1), (1383036028334774549, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_2, prime_t53_5, prime_t53_2969, prime_lucas_1383036028334774549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t53_328498717450075650878481 : Nat.totient 328498717450075650878481 = 218999144966717100585636 := by
  rw [← show ((([(3, 3), (12166619164817616699203, 1)] : List FactorBlock).map factorBlockValue).prod) = 328498717450075650878481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t53_3, prime_lucas_12166619164817616699203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twenty-fifth finite diagonal certificate -/

theorem certifiedKill_diagonal_t53 :
    certifiedKill (periodLcm 53) (periodLcm 53) 81 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t53_164249358725037825439201, phi_t53_164249358725037825439202, phi_t53_164249358725037825439203, phi_t53_164249358725037825439204, phi_t53_164249358725037825439205, phi_t53_164249358725037825439206, phi_t53_164249358725037825439207, phi_t53_164249358725037825439208, phi_t53_164249358725037825439209, phi_t53_164249358725037825439210, phi_t53_164249358725037825439211, phi_t53_164249358725037825439212, phi_t53_164249358725037825439213, phi_t53_164249358725037825439214, phi_t53_164249358725037825439215, phi_t53_164249358725037825439216, phi_t53_164249358725037825439217, phi_t53_164249358725037825439218, phi_t53_164249358725037825439219, phi_t53_164249358725037825439220, phi_t53_164249358725037825439221, phi_t53_164249358725037825439222, phi_t53_164249358725037825439223, phi_t53_164249358725037825439224, phi_t53_164249358725037825439225, phi_t53_164249358725037825439226, phi_t53_164249358725037825439227, phi_t53_164249358725037825439228, phi_t53_164249358725037825439229, phi_t53_164249358725037825439230, phi_t53_164249358725037825439231, phi_t53_164249358725037825439232, phi_t53_164249358725037825439233, phi_t53_164249358725037825439234, phi_t53_164249358725037825439235, phi_t53_164249358725037825439236, phi_t53_164249358725037825439237, phi_t53_164249358725037825439238, phi_t53_164249358725037825439239, phi_t53_164249358725037825439240, phi_t53_164249358725037825439241, phi_t53_164249358725037825439242, phi_t53_164249358725037825439243, phi_t53_164249358725037825439244, phi_t53_164249358725037825439245, phi_t53_164249358725037825439246, phi_t53_164249358725037825439247, phi_t53_164249358725037825439248, phi_t53_164249358725037825439249, phi_t53_164249358725037825439250, phi_t53_164249358725037825439251, phi_t53_164249358725037825439252, phi_t53_164249358725037825439253, phi_t53_164249358725037825439254, phi_t53_164249358725037825439255, phi_t53_164249358725037825439256, phi_t53_164249358725037825439257, phi_t53_164249358725037825439258, phi_t53_164249358725037825439259, phi_t53_164249358725037825439260, phi_t53_164249358725037825439261, phi_t53_164249358725037825439262, phi_t53_164249358725037825439263, phi_t53_164249358725037825439264, phi_t53_164249358725037825439265, phi_t53_164249358725037825439266, phi_t53_164249358725037825439267, phi_t53_164249358725037825439268, phi_t53_164249358725037825439269, phi_t53_164249358725037825439270, phi_t53_164249358725037825439271, phi_t53_164249358725037825439272, phi_t53_164249358725037825439273, phi_t53_164249358725037825439274, phi_t53_164249358725037825439275, phi_t53_164249358725037825439276, phi_t53_164249358725037825439277, phi_t53_164249358725037825439278, phi_t53_164249358725037825439279, phi_t53_164249358725037825439280, phi_t53_164249358725037825439281, phi_t53_328498717450075650878401, phi_t53_328498717450075650878402, phi_t53_328498717450075650878403, phi_t53_328498717450075650878404, phi_t53_328498717450075650878405, phi_t53_328498717450075650878406, phi_t53_328498717450075650878407, phi_t53_328498717450075650878408, phi_t53_328498717450075650878409, phi_t53_328498717450075650878410, phi_t53_328498717450075650878411, phi_t53_328498717450075650878412, phi_t53_328498717450075650878413, phi_t53_328498717450075650878414, phi_t53_328498717450075650878415, phi_t53_328498717450075650878416, phi_t53_328498717450075650878417, phi_t53_328498717450075650878418, phi_t53_328498717450075650878419, phi_t53_328498717450075650878420, phi_t53_328498717450075650878421, phi_t53_328498717450075650878422, phi_t53_328498717450075650878423, phi_t53_328498717450075650878424, phi_t53_328498717450075650878425, phi_t53_328498717450075650878426, phi_t53_328498717450075650878427, phi_t53_328498717450075650878428, phi_t53_328498717450075650878429, phi_t53_328498717450075650878430, phi_t53_328498717450075650878431, phi_t53_328498717450075650878432, phi_t53_328498717450075650878433, phi_t53_328498717450075650878434, phi_t53_328498717450075650878435, phi_t53_328498717450075650878436, phi_t53_328498717450075650878437, phi_t53_328498717450075650878438, phi_t53_328498717450075650878439, phi_t53_328498717450075650878440, phi_t53_328498717450075650878441, phi_t53_328498717450075650878442, phi_t53_328498717450075650878443, phi_t53_328498717450075650878444, phi_t53_328498717450075650878445, phi_t53_328498717450075650878446, phi_t53_328498717450075650878447, phi_t53_328498717450075650878448, phi_t53_328498717450075650878449, phi_t53_328498717450075650878450, phi_t53_328498717450075650878451, phi_t53_328498717450075650878452, phi_t53_328498717450075650878453, phi_t53_328498717450075650878454, phi_t53_328498717450075650878455, phi_t53_328498717450075650878456, phi_t53_328498717450075650878457, phi_t53_328498717450075650878458, phi_t53_328498717450075650878459, phi_t53_328498717450075650878460, phi_t53_328498717450075650878461, phi_t53_328498717450075650878462, phi_t53_328498717450075650878463, phi_t53_328498717450075650878464, phi_t53_328498717450075650878465, phi_t53_328498717450075650878466, phi_t53_328498717450075650878467, phi_t53_328498717450075650878468, phi_t53_328498717450075650878469, phi_t53_328498717450075650878470, phi_t53_328498717450075650878471, phi_t53_328498717450075650878472, phi_t53_328498717450075650878473, phi_t53_328498717450075650878474, phi_t53_328498717450075650878475, phi_t53_328498717450075650878476, phi_t53_328498717450075650878477, phi_t53_328498717450075650878478, phi_t53_328498717450075650878479, phi_t53_328498717450075650878480, phi_t53_328498717450075650878481]

def diagonalPincerCertificateScalesThroughT53 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53]

def diagonalPincerKillDepthThroughT53 : ℕ → ℕ
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
  | _ => 0

/-- All 25 imported scales through t=53 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t53 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT53,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT53 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT53, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t37
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t41
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t43
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t47
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t49
  · simpa [diagonalPincerKillDepthThroughT53] using certifiedKill_diagonal_t53

#print axioms certifiedKill_diagonal_all_imported_through_t53

end TotientTailPeriodKiller
end Erdos249257
