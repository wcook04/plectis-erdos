import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT41

/-!
# A free-position kill above 10^17

This certificate uses the position two integers before `periodLcm 41`, while
the shift is only one.  The long factored block from the public t=41
certificate supplies the positive offsets; two explicit factor-block
reconstructions close the left edge.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open private
  phi_t41_219060189739591201 phi_t41_219060189739591202
  phi_t41_219060189739591203 phi_t41_219060189739591204
  phi_t41_219060189739591205 phi_t41_219060189739591206
  phi_t41_219060189739591207 phi_t41_219060189739591208
  phi_t41_219060189739591209 phi_t41_219060189739591210
  phi_t41_219060189739591211 phi_t41_219060189739591212
  phi_t41_219060189739591213 phi_t41_219060189739591214
  phi_t41_219060189739591215 phi_t41_219060189739591216
  phi_t41_219060189739591217 phi_t41_219060189739591218
  phi_t41_219060189739591219 phi_t41_219060189739591220
  phi_t41_219060189739591221 phi_t41_219060189739591222
  phi_t41_219060189739591223 phi_t41_219060189739591224
  phi_t41_219060189739591225 phi_t41_219060189739591226
  phi_t41_219060189739591227 phi_t41_219060189739591228
  phi_t41_219060189739591229 phi_t41_219060189739591230
  phi_t41_219060189739591231 phi_t41_219060189739591232
  phi_t41_219060189739591233 phi_t41_219060189739591234
  phi_t41_219060189739591235 phi_t41_219060189739591236
  phi_t41_219060189739591237 phi_t41_219060189739591238
  phi_t41_219060189739591239 phi_t41_219060189739591240
  phi_t41_219060189739591241 phi_t41_219060189739591242
  phi_t41_219060189739591243 phi_t41_219060189739591244
  phi_t41_219060189739591245 phi_t41_219060189739591246
  phi_t41_219060189739591247 phi_t41_219060189739591248
  phi_t41_219060189739591249 phi_t41_219060189739591250
  phi_t41_219060189739591251 phi_t41_219060189739591252
  phi_t41_219060189739591253 phi_t41_219060189739591254
  phi_t41_219060189739591255 phi_t41_219060189739591256
  phi_t41_219060189739591257 phi_t41_219060189739591258
  phi_t41_219060189739591259 phi_t41_219060189739591260
  phi_t41_219060189739591261
  from Erdos249257.DiagonalPincerCertificatesT41

private theorem prime_free18B_2 : Nat.Prime 2 := by norm_num
private theorem prime_free18B_3 : Nat.Prime 3 := by norm_num
private theorem prime_free18B_5 : Nat.Prime 5 := by norm_num
private theorem prime_free18B_7 : Nat.Prime 7 := by norm_num
private theorem prime_free18B_11 : Nat.Prime 11 := by norm_num
private theorem prime_free18B_13 : Nat.Prime 13 := by norm_num
private theorem prime_free18B_17 : Nat.Prime 17 := by norm_num
private theorem prime_free18B_19 : Nat.Prime 19 := by norm_num
private theorem prime_free18B_23 : Nat.Prime 23 := by norm_num
private theorem prime_free18B_29 : Nat.Prime 29 := by norm_num
private theorem prime_free18B_31 : Nat.Prime 31 := by norm_num
private theorem prime_free18B_37 : Nat.Prime 37 := by norm_num
private theorem prime_free18B_41 : Nat.Prime 41 := by norm_num
private theorem prime_free18B_232457 : Nat.Prime 232457 := by norm_num
private theorem prime_free18B_695377 : Nat.Prime 695377 := by norm_num
private theorem prime_free18B_1355191 : Nat.Prime 1355191 := by norm_num

private theorem phi_free18B_219060189739591199 :
    Nat.totient 219060189739591199 = 219058770704336640 := by
  rw [← show
    ((([(232457, 1), (695377, 1), (1355191, 1)] : List FactorBlock).map
      factorBlockValue).prod) = 219060189739591199 by
        norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free18B_232457, prime_free18B_695377, prime_free18B_1355191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free18B_219060189739591200 :
    Nat.totient 219060189739591200 = 31784246968320000 := by
  rw [← show
    ((([(2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1),
      (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1)] :
      List FactorBlock).map factorBlockValue).prod) = 219060189739591200 by
        norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free18B_2, prime_free18B_3, prime_free18B_5, prime_free18B_7,
      prime_free18B_11, prime_free18B_13, prime_free18B_17, prime_free18B_19,
      prime_free18B_23, prime_free18B_29, prime_free18B_31, prime_free18B_37,
      prime_free18B_41]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-- An off-diagonal free-position kill: the shift is `1`, while the position
is `periodLcm 41 - 2`. -/
theorem freeKill_18B : certifiedKill 1 219060189739591198 62 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_free18B_219060189739591199, phi_free18B_219060189739591200,
    phi_t41_219060189739591201, phi_t41_219060189739591202,
    phi_t41_219060189739591203, phi_t41_219060189739591204,
    phi_t41_219060189739591205, phi_t41_219060189739591206,
    phi_t41_219060189739591207, phi_t41_219060189739591208,
    phi_t41_219060189739591209, phi_t41_219060189739591210,
    phi_t41_219060189739591211, phi_t41_219060189739591212,
    phi_t41_219060189739591213, phi_t41_219060189739591214,
    phi_t41_219060189739591215, phi_t41_219060189739591216,
    phi_t41_219060189739591217, phi_t41_219060189739591218,
    phi_t41_219060189739591219, phi_t41_219060189739591220,
    phi_t41_219060189739591221, phi_t41_219060189739591222,
    phi_t41_219060189739591223, phi_t41_219060189739591224,
    phi_t41_219060189739591225, phi_t41_219060189739591226,
    phi_t41_219060189739591227, phi_t41_219060189739591228,
    phi_t41_219060189739591229, phi_t41_219060189739591230,
    phi_t41_219060189739591231, phi_t41_219060189739591232,
    phi_t41_219060189739591233, phi_t41_219060189739591234,
    phi_t41_219060189739591235, phi_t41_219060189739591236,
    phi_t41_219060189739591237, phi_t41_219060189739591238,
    phi_t41_219060189739591239, phi_t41_219060189739591240,
    phi_t41_219060189739591241, phi_t41_219060189739591242,
    phi_t41_219060189739591243, phi_t41_219060189739591244,
    phi_t41_219060189739591245, phi_t41_219060189739591246,
    phi_t41_219060189739591247, phi_t41_219060189739591248,
    phi_t41_219060189739591249, phi_t41_219060189739591250,
    phi_t41_219060189739591251, phi_t41_219060189739591252,
    phi_t41_219060189739591253, phi_t41_219060189739591254,
    phi_t41_219060189739591255, phi_t41_219060189739591256,
    phi_t41_219060189739591257, phi_t41_219060189739591258,
    phi_t41_219060189739591259, phi_t41_219060189739591260,
    phi_t41_219060189739591261]

end TotientTailPeriodKiller
end Erdos249257
