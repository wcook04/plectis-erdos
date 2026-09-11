import Erdos249257.DiagonalPincerCertificatesT32
import Erdos249257.DiagonalPincerPrimeCertificates.Prime38763509
import Erdos249257.DiagonalPincerPrimeCertificates.Prime46640743
import Erdos249257.DiagonalPincerPrimeCertificates.Prime49732087
import Erdos249257.DiagonalPincerPrimeCertificates.Prime62986559
import Erdos249257.DiagonalPincerPrimeCertificates.Prime96946471
import Erdos249257.DiagonalPincerPrimeCertificates.Prime104258953
import Erdos249257.DiagonalPincerPrimeCertificates.Prime138639701
import Erdos249257.DiagonalPincerPrimeCertificates.Prime169653067
import Erdos249257.DiagonalPincerPrimeCertificates.Prime192059807
import Erdos249257.DiagonalPincerPrimeCertificates.Prime272205859
import Erdos249257.DiagonalPincerPrimeCertificates.Prime285719971
import Erdos249257.DiagonalPincerPrimeCertificates.Prime320796191
import Erdos249257.DiagonalPincerPrimeCertificates.Prime356495017
import Erdos249257.DiagonalPincerPrimeCertificates.Prime716333897
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1202644063
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2064151171
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2297338423
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2619709439
import Erdos249257.DiagonalPincerPrimeCertificates.Prime4579662077
import Erdos249257.DiagonalPincerPrimeCertificates.Prime6268202813
import Erdos249257.DiagonalPincerPrimeCertificates.Prime6752357867
import Erdos249257.DiagonalPincerPrimeCertificates.Prime7996526947
import Erdos249257.DiagonalPincerPrimeCertificates.Prime8197540487
import Erdos249257.DiagonalPincerPrimeCertificates.Prime9191096507
import Erdos249257.DiagonalPincerPrimeCertificates.Prime22179871631
import Erdos249257.DiagonalPincerPrimeCertificates.Prime33463490363
import Erdos249257.DiagonalPincerPrimeCertificates.Prime59723582981
import Erdos249257.DiagonalPincerPrimeCertificates.Prime69787961743
import Erdos249257.DiagonalPincerPrimeCertificates.Prime75691781281
import Erdos249257.DiagonalPincerPrimeCertificates.Prime112611974941
import Erdos249257.DiagonalPincerPrimeCertificates.Prime153581058871
import Erdos249257.DiagonalPincerPrimeCertificates.Prime172363747889
import Erdos249257.DiagonalPincerPrimeCertificates.Prime175520489383
import Erdos249257.DiagonalPincerPrimeCertificates.Prime241745196347
import Erdos249257.DiagonalPincerPrimeCertificates.Prime830098882477
import Erdos249257.DiagonalPincerPrimeCertificates.Prime930419060873
import Erdos249257.DiagonalPincerPrimeCertificates.Prime1413847964293
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2147912143543
import Erdos249257.DiagonalPincerPrimeCertificates.Prime2150073020951
import Erdos249257.DiagonalPincerPrimeCertificates.Prime3667077183983
import Erdos249257.DiagonalPincerPrimeCertificates.Prime8322323141843
import Erdos249257.DiagonalPincerPrimeCertificates.Prime11453229275591
import Erdos249257.DiagonalPincerPrimeCertificates.Prime26581748542603
import Erdos249257.DiagonalPincerPrimeCertificates.Prime29437638881891
import Erdos249257.DiagonalPincerPrimeCertificates.Prime29600728293979
import Erdos249257.DiagonalPincerPrimeCertificates.Prime30883996861637
import Erdos249257.DiagonalPincerPrimeCertificates.Prime54519708745543
import Erdos249257.DiagonalPincerPrimeCertificates.Prime83483304016613
import Erdos249257.DiagonalPincerPrimeCertificates.Prime97144208310241
import Erdos249257.DiagonalPincerPrimeCertificates.Prime105800622912143
import Erdos249257.DiagonalPincerPrimeCertificates.Prime116150683849201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime118731810156961
import Erdos249257.DiagonalPincerPrimeCertificates.Prime120065875439623
import Erdos249257.DiagonalPincerPrimeCertificates.Prime148414762696201
import Erdos249257.DiagonalPincerPrimeCertificates.Prime157145042854801
import Erdos249257.DiagonalPincerPrimeCertificates.Prime161907013850401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime194288416620481
import Erdos249257.DiagonalPincerPrimeCertificates.Prime209526723806401
import Erdos249257.DiagonalPincerPrimeCertificates.Prime237463620313921
import Erdos249257.DiagonalPincerPrimeCertificates.Prime667866432132901
import Erdos249257.DiagonalPincerPrimeCertificates.Prime5342931457063253

/-!
# The t=37 diagonal-pincer certificate

This generated extension consumes 61 new large-prime Lucas roots
and 27 recursive Pratt dependencies, reuses 1 earlier certificates,
reconstructs all 112 Euler totients in the t=37 window, and proves the
twentieth finite diagonal kill without `native evaluation`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=37 window -/

private theorem prime_t37_2 : Nat.Prime 2 := by norm_num
private theorem prime_t37_3 : Nat.Prime 3 := by norm_num
private theorem prime_t37_5 : Nat.Prime 5 := by norm_num
private theorem prime_t37_7 : Nat.Prime 7 := by norm_num
private theorem prime_t37_11 : Nat.Prime 11 := by norm_num
private theorem prime_t37_13 : Nat.Prime 13 := by norm_num
private theorem prime_t37_17 : Nat.Prime 17 := by norm_num
private theorem prime_t37_19 : Nat.Prime 19 := by norm_num
private theorem prime_t37_23 : Nat.Prime 23 := by norm_num
private theorem prime_t37_29 : Nat.Prime 29 := by norm_num
private theorem prime_t37_31 : Nat.Prime 31 := by norm_num
private theorem prime_t37_37 : Nat.Prime 37 := by norm_num
private theorem prime_t37_41 : Nat.Prime 41 := by norm_num
private theorem prime_t37_43 : Nat.Prime 43 := by norm_num
private theorem prime_t37_47 : Nat.Prime 47 := by norm_num
private theorem prime_t37_53 : Nat.Prime 53 := by norm_num
private theorem prime_t37_59 : Nat.Prime 59 := by norm_num
private theorem prime_t37_61 : Nat.Prime 61 := by norm_num
private theorem prime_t37_67 : Nat.Prime 67 := by norm_num
private theorem prime_t37_71 : Nat.Prime 71 := by norm_num
private theorem prime_t37_79 : Nat.Prime 79 := by norm_num
private theorem prime_t37_83 : Nat.Prime 83 := by norm_num
private theorem prime_t37_89 : Nat.Prime 89 := by norm_num
private theorem prime_t37_97 : Nat.Prime 97 := by norm_num
private theorem prime_t37_101 : Nat.Prime 101 := by norm_num
private theorem prime_t37_107 : Nat.Prime 107 := by norm_num
private theorem prime_t37_109 : Nat.Prime 109 := by norm_num
private theorem prime_t37_137 : Nat.Prime 137 := by norm_num
private theorem prime_t37_149 : Nat.Prime 149 := by norm_num
private theorem prime_t37_157 : Nat.Prime 157 := by norm_num
private theorem prime_t37_163 : Nat.Prime 163 := by norm_num
private theorem prime_t37_173 : Nat.Prime 173 := by norm_num
private theorem prime_t37_193 : Nat.Prime 193 := by norm_num
private theorem prime_t37_199 : Nat.Prime 199 := by norm_num
private theorem prime_t37_211 : Nat.Prime 211 := by norm_num
private theorem prime_t37_223 : Nat.Prime 223 := by norm_num
private theorem prime_t37_251 : Nat.Prime 251 := by norm_num
private theorem prime_t37_281 : Nat.Prime 281 := by norm_num
private theorem prime_t37_311 : Nat.Prime 311 := by norm_num
private theorem prime_t37_317 : Nat.Prime 317 := by norm_num
private theorem prime_t37_347 : Nat.Prime 347 := by norm_num
private theorem prime_t37_353 : Nat.Prime 353 := by norm_num
private theorem prime_t37_397 : Nat.Prime 397 := by norm_num
private theorem prime_t37_439 : Nat.Prime 439 := by norm_num
private theorem prime_t37_449 : Nat.Prime 449 := by norm_num
private theorem prime_t37_461 : Nat.Prime 461 := by norm_num
private theorem prime_t37_523 : Nat.Prime 523 := by norm_num
private theorem prime_t37_613 : Nat.Prime 613 := by norm_num
private theorem prime_t37_653 : Nat.Prime 653 := by norm_num
private theorem prime_t37_661 : Nat.Prime 661 := by norm_num
private theorem prime_t37_769 : Nat.Prime 769 := by norm_num
private theorem prime_t37_877 : Nat.Prime 877 := by norm_num
private theorem prime_t37_983 : Nat.Prime 983 := by norm_num
private theorem prime_t37_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_t37_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_t37_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_t37_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_t37_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_t37_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_t37_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_t37_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_t37_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_t37_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_t37_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_t37_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_t37_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_t37_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_t37_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_t37_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_t37_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_t37_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_t37_2699 : Nat.Prime 2699 := by norm_num
private theorem prime_t37_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_t37_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_t37_3187 : Nat.Prime 3187 := by norm_num
private theorem prime_t37_3449 : Nat.Prime 3449 := by norm_num
private theorem prime_t37_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_t37_3989 : Nat.Prime 3989 := by norm_num
private theorem prime_t37_4261 : Nat.Prime 4261 := by norm_num
private theorem prime_t37_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_t37_6883 : Nat.Prime 6883 := by norm_num
private theorem prime_t37_8317 : Nat.Prime 8317 := by norm_num
private theorem prime_t37_9007 : Nat.Prime 9007 := by norm_num
private theorem prime_t37_10243 : Nat.Prime 10243 := by norm_num
private theorem prime_t37_10627 : Nat.Prime 10627 := by norm_num
private theorem prime_t37_11113 : Nat.Prime 11113 := by norm_num
private theorem prime_t37_11471 : Nat.Prime 11471 := by norm_num
private theorem prime_t37_11827 : Nat.Prime 11827 := by norm_num
private theorem prime_t37_12919 : Nat.Prime 12919 := by norm_num
private theorem prime_t37_13103 : Nat.Prime 13103 := by norm_num
private theorem prime_t37_15199 : Nat.Prime 15199 := by norm_num
private theorem prime_t37_16087 : Nat.Prime 16087 := by norm_num
private theorem prime_t37_18379 : Nat.Prime 18379 := by norm_num
private theorem prime_t37_19727 : Nat.Prime 19727 := by norm_num
private theorem prime_t37_34403 : Nat.Prime 34403 := by norm_num
private theorem prime_t37_36919 : Nat.Prime 36919 := by norm_num
private theorem prime_t37_37441 : Nat.Prime 37441 := by norm_num
private theorem prime_t37_39139 : Nat.Prime 39139 := by norm_num
private theorem prime_t37_44203 : Nat.Prime 44203 := by norm_num
private theorem prime_t37_45317 : Nat.Prime 45317 := by norm_num
private theorem prime_t37_52783 : Nat.Prime 52783 := by norm_num
private theorem prime_t37_53441 : Nat.Prime 53441 := by norm_num
private theorem prime_t37_55817 : Nat.Prime 55817 := by norm_num
private theorem prime_t37_105467 : Nat.Prime 105467 := by norm_num
private theorem prime_t37_124601 : Nat.Prime 124601 := by norm_num
private theorem prime_t37_154153 : Nat.Prime 154153 := by norm_num
private theorem prime_t37_155047 : Nat.Prime 155047 := by norm_num
private theorem prime_t37_171043 : Nat.Prime 171043 := by norm_num
private theorem prime_t37_179057 : Nat.Prime 179057 := by norm_num
private theorem prime_t37_243539 : Nat.Prime 243539 := by norm_num
private theorem prime_t37_270437 : Nat.Prime 270437 := by norm_num
private theorem prime_t37_291359 : Nat.Prime 291359 := by norm_num
private theorem prime_t37_295553 : Nat.Prime 295553 := by norm_num
private theorem prime_t37_365231 : Nat.Prime 365231 := by norm_num
private theorem prime_t37_384941 : Nat.Prime 384941 := by norm_num
private theorem prime_t37_573763 : Nat.Prime 573763 := by norm_num
private theorem prime_t37_596749 : Nat.Prime 596749 := by norm_num
private theorem prime_t37_663037 : Nat.Prime 663037 := by norm_num
private theorem prime_t37_785579 : Nat.Prime 785579 := by norm_num
private theorem prime_t37_790753 : Nat.Prime 790753 := by norm_num
private theorem prime_t37_873113 : Nat.Prime 873113 := by norm_num
private theorem prime_t37_901183 : Nat.Prime 901183 := by norm_num
private theorem prime_t37_1394683 : Nat.Prime 1394683 := by norm_num
private theorem prime_t37_1589663 : Nat.Prime 1589663 := by norm_num
private theorem prime_t37_1855093 : Nat.Prime 1855093 := by norm_num
private theorem prime_t37_2051263 : Nat.Prime 2051263 := by norm_num
private theorem prime_t37_2305753 : Nat.Prime 2305753 := by norm_num
private theorem prime_t37_2562337 : Nat.Prime 2562337 := by norm_num
private theorem prime_t37_4773269 : Nat.Prime 4773269 := by norm_num
private theorem prime_t37_5483719 : Nat.Prime 5483719 := by norm_num
private theorem prime_t37_6940783 : Nat.Prime 6940783 := by norm_num
private theorem prime_t37_7148261 : Nat.Prime 7148261 := by norm_num
private theorem prime_t37_10665041 : Nat.Prime 10665041 := by norm_num
private theorem prime_t37_10941097 : Nat.Prime 10941097 := by norm_num
private theorem prime_t37_12912187 : Nat.Prime 12912187 := by norm_num
private theorem prime_t37_14373941 : Nat.Prime 14373941 := by norm_num
private theorem prime_t37_28677119 : Nat.Prime 28677119 := by norm_num
private theorem prime_t37_29456429 : Nat.Prime 29456429 := by norm_num
private theorem prime_t37_30629789 : Nat.Prime 30629789 := by norm_num
private theorem prime_t37_31311011 : Nat.Prime 31311011 := by norm_num
private theorem prime_t37_32730007 : Nat.Prime 32730007 := by norm_num

/-! ## Exact t=37 window totients -/

private theorem phi_t37_5342931457063201 : Nat.totient 5342931457063201 = 5312047460201392 := by
  rw [← show ((([(173, 1), (30883996861637, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_173, prime_lucas_30883996861637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063202 : Nat.totient 5342931457063202 = 2667724300633392 := by
  rw [← show ((([(2, 1), (1109, 1), (2003, 1), (1202644063, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_1109, prime_t37_2003, prime_lucas_1202644063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063203 : Nat.totient 5342931457063203 = 3508790807623464 := by
  rw [← show ((([(3, 1), (67, 1), (26581748542603, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_67, prime_lucas_26581748542603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063204 : Nat.totient 5342931457063204 = 2637880275115008 := by
  rw [← show ((([(2, 2), (83, 1), (2447, 1), (8317, 1), (790753, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_83, prime_t37_2447, prime_t37_8317, prime_t37_790753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063205 : Nat.totient 5342931457063205 = 4255788373985280 := by
  rw [← show ((([(5, 1), (353, 1), (661, 1), (4579662077, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_353, prime_t37_661, prime_lucas_4579662077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063206 : Nat.totient 5342931457063206 = 1764332506070504 := by
  rw [← show ((([(2, 1), (3, 1), (107, 1), (8322323141843, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_107, prime_lucas_8322323141843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063207 : Nat.totient 5342931457063207 = 4579639814620824 := by
  rw [← show ((([(7, 1), (291359, 1), (2619709439, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_7, prime_t37_291359, prime_lucas_2619709439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063208 : Nat.totient 5342931457063208 = 2671465728531600 := by
  rw [← show ((([(2, 3), (667866432132901, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_lucas_667866432132901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063209 : Nat.totient 5342931457063209 = 3551174405775360 := by
  rw [← show ((([(3, 2), (769, 1), (1093, 1), (1231, 1), (573763, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_769, prime_t37_1093, prime_t37_1231, prime_t37_573763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063210 : Nat.totient 5342931457063210 = 2129353644531456 := by
  rw [← show ((([(2, 1), (5, 1), (317, 1), (2437, 1), (13103, 1), (52783, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_317, prime_t37_2437, prime_t37_13103, prime_t37_52783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063211 : Nat.totient 5342931457063211 = 4844741052465600 := by
  rw [← show ((([(11, 1), (439, 1), (3449, 1), (320796191, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_11, prime_t37_439, prime_t37_3449, prime_lucas_320796191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063212 : Nat.totient 5342931457063212 = 1764690529152000 := by
  rw [← show ((([(2, 2), (3, 1), (193, 1), (251, 1), (9191096507, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_193, prime_t37_251, prime_lucas_9191096507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063213 : Nat.totient 5342931457063213 = 4841864341434432 := by
  rw [← show ((([(13, 2), (59, 1), (983, 1), (3187, 1), (171043, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_13, prime_t37_59, prime_t37_983, prime_t37_3187, prime_t37_171043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063214 : Nat.totient 5342931457063214 = 2289827767312764 := by
  rw [← show ((([(2, 1), (7, 2), (54519708745543, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_7, prime_lucas_54519708745543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063215 : Nat.totient 5342931457063215 = 2849545063819296 := by
  rw [← show ((([(3, 1), (5, 1), (155047, 1), (2297338423, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_5, prime_t37_155047, prime_lucas_2297338423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063216 : Nat.totient 5342931457063216 = 2671465392723200 := by
  rw [← show ((([(2, 4), (10665041, 1), (31311011, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_10665041, prime_t37_31311011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063217 : Nat.totient 5342931457063217 = 5026987408101120 := by
  rw [← show ((([(17, 1), (4261, 1), (10627, 1), (6940783, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_17, prime_t37_4261, prime_t37_10627, prime_t37_6940783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063218 : Nat.totient 5342931457063218 = 1779620072797728 := by
  rw [← show ((([(2, 1), (3, 2), (1429, 1), (16087, 1), (12912187, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_1429, prime_t37_16087, prime_t37_12912187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063219 : Nat.totient 5342931457063219 = 5058960079177800 := by
  rw [← show ((([(19, 1), (1831, 1), (153581058871, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_19, prime_t37_1831, prime_lucas_153581058871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063220 : Nat.totient 5342931457063220 = 2137171728254976 := by
  rw [← show ((([(2, 2), (5, 1), (2562337, 1), (104258953, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_2562337, prime_lucas_104258953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063221 : Nat.totient 5342931457063221 = 3052837531153200 := by
  rw [← show ((([(3, 1), (7, 1), (11471, 1), (22179871631, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_7, prime_t37_11471, prime_lucas_22179871631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063222 : Nat.totient 5342931457063222 = 2426881570263040 := by
  rw [← show ((([(2, 1), (11, 1), (1409, 1), (172363747889, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_11, prime_t37_1409, prime_lucas_172363747889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063223 : Nat.totient 5342931457063223 = 5110481536734904 := by
  rw [← show ((([(23, 1), (34403, 1), (6752357867, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_23, prime_t37_34403, prime_lucas_6752357867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063224 : Nat.totient 5342931457063224 = 1776971235508224 := by
  rw [← show ((([(2, 3), (3, 1), (449, 1), (45317, 1), (10941097, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_449, prime_t37_45317, prime_t37_10941097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063225 : Nat.totient 5342931457063225 = 4184348449176000 := by
  rw [← show ((([(5, 2), (61, 2), (211, 1), (272205859, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_61, prime_t37_211, prime_lucas_272205859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063226 : Nat.totient 5342931457063226 = 2372503634542080 := by
  rw [← show ((([(2, 1), (13, 1), (41, 1), (79, 1), (1279, 1), (2699, 1), (18379, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_13, prime_t37_41, prime_t37_79, prime_t37_1279, prime_t37_2699, prime_t37_18379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063227 : Nat.totient 5342931457063227 = 3492263230709760 := by
  rw [← show ((([(3, 6), (53, 1), (2287, 1), (5441, 1), (11113, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_53, prime_t37_2287, prime_t37_5441, prime_t37_11113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063228 : Nat.totient 5342931457063228 = 2288919465907200 := by
  rw [← show ((([(2, 2), (7, 1), (2521, 1), (75691781281, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_7, prime_t37_2521, prime_lucas_75691781281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063229 : Nat.totient 5342931457063229 = 5034285587100672 := by
  rw [← show ((([(29, 1), (43, 1), (1213, 1), (19727, 1), (179057, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_29, prime_t37_43, prime_t37_1213, prime_t37_19727, prime_t37_179057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063230 : Nat.totient 5342931457063230 = 1410055027928064 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (97, 1), (36919, 1), (49732087, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_5, prime_t37_97, prime_t37_36919, prime_lucas_49732087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063231 : Nat.totient 5342931457063231 = 5060566513895160 := by
  rw [← show ((([(31, 1), (47, 1), (3667077183983, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_31, prime_t37_47, prime_lucas_3667077183983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063232 : Nat.totient 5342931457063232 = 2671465728531584 := by
  rw [← show ((([(2, 6), (83483304016613, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_lucas_83483304016613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063233 : Nat.totient 5342931457063233 = 3238140277008000 := by
  rw [← show ((([(3, 1), (11, 1), (161907013850401, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_11, prime_lucas_161907013850401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063234 : Nat.totient 5342931457063234 = 2514320685676800 := by
  rw [← show ((([(2, 1), (17, 1), (157145042854801, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_17, prime_lucas_157145042854801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063235 : Nat.totient 5342931457063235 = 3612122675196000 := by
  rw [← show ((([(5, 1), (7, 1), (71, 1), (2150073020951, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_7, prime_t37_71, prime_lucas_2150073020951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063236 : Nat.totient 5342931457063236 = 1780977152354400 := by
  rw [← show ((([(2, 2), (3, 2), (148414762696201, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_lucas_148414762696201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063237 : Nat.totient 5342931457063237 = 5195641436640000 := by
  rw [← show ((([(37, 1), (1801, 1), (80179651801, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_37, prime_t37_1801, prime_lucas_80179651801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063238 : Nat.totient 5342931457063238 = 2530861653000672 := by
  rw [← show ((([(2, 1), (19, 1), (4773269, 1), (29456429, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_19, prime_t37_4773269, prime_t37_29456429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063239 : Nat.totient 5342931457063239 = 3257787118209408 := by
  rw [← show ((([(3, 1), (13, 1), (109, 1), (901183, 1), (1394683, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_13, prime_t37_109, prime_t37_901183, prime_t37_1394683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063240 : Nat.totient 5342931457063240 = 2118710813725440 := by
  rw [← show ((([(2, 3), (5, 1), (163, 1), (397, 1), (2064151171, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_163, prime_t37_397, prime_lucas_2064151171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063241 : Nat.totient 5342931457063241 = 5295809550002560 := by
  rw [← show ((([(137, 1), (653, 1), (59723582981, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_137, prime_t37_653, prime_lucas_59723582981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063242 : Nat.totient 5342931457063242 = 1526138039070720 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (3989, 1), (53441, 1), (596749, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_7, prime_t37_3989, prime_t37_53441, prime_t37_596749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063243 : Nat.totient 5342931457063243 = 5323909250869440 := by
  rw [← show ((([(281, 1), (663037, 1), (28677119, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_281, prime_t37_663037, prime_t37_28677119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063244 : Nat.totient 5342931457063244 = 2423950316144640 := by
  rw [← show ((([(2, 2), (11, 1), (523, 1), (295553, 1), (785579, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_11, prime_t37_523, prime_t37_295553, prime_t37_785579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063245 : Nat.totient 5342931457063245 = 2849563443767040 := by
  rw [← show ((([(3, 2), (5, 1), (118731810156961, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_5, prime_lucas_118731810156961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063246 : Nat.totient 5342931457063246 = 2555315044682400 := by
  rw [← show ((([(2, 1), (23, 1), (116150683849201, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_23, prime_lucas_116150683849201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063247 : Nat.totient 5342931457063247 = 5341517609095176 := by
  rw [← show ((([(3779, 1), (1413847964293, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3779, prime_lucas_1413847964293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063248 : Nat.totient 5342931457063248 = 1771975824186240 := by
  rw [← show ((([(2, 4), (3, 1), (223, 1), (1747, 1), (285719971, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_223, prime_t37_1747, prime_lucas_285719971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063249 : Nat.totient 5342931457063249 = 4579438634035200 := by
  rw [← show ((([(7, 1), (37441, 1), (55817, 1), (365231, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_7, prime_t37_37441, prime_t37_55817, prime_t37_365231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063250 : Nat.totient 5342931457063250 = 2137158703440000 := by
  rw [← show ((([(2, 1), (5, 3), (154153, 1), (138639701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_154153, prime_lucas_138639701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063251 : Nat.totient 5342931457063251 = 3330590547847680 := by
  rw [← show ((([(3, 1), (17, 1), (157, 1), (6883, 1), (96946471, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_17, prime_t37_157, prime_t37_6883, prime_lucas_96946471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063252 : Nat.totient 5342931457063252 = 2465967848265600 := by
  rw [← show ((([(2, 2), (13, 1), (7148261, 1), (14373941, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_13, prime_t37_7148261, prime_t37_14373941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063253 : Nat.totient 5342931457063253 = 5342931457063252 := by
  rw [← show ((([(5342931457063253, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_5342931457063253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063254 : Nat.totient 5342931457063254 = 1777068132095520 := by
  rw [← show ((([(2, 1), (3, 3), (461, 1), (39139, 1), (5483719, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_461, prime_t37_39139, prime_t37_5483719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063255 : Nat.totient 5342931457063255 = 3885768332409600 := by
  rw [← show ((([(5, 1), (11, 1), (97144208310241, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_11, prime_lucas_97144208310241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_5342931457063256 : Nat.totient 5342931457063256 = 2287195813324800 := by
  rw [← show ((([(2, 3), (7, 1), (877, 1), (124601, 1), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 5342931457063256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_7, prime_t37_877, prime_t37_124601, prime_t37_873113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126401 : Nat.totient 10685862914126401 = 10408365892907008 := by
  rw [← show ((([(53, 1), (149, 1), (1889, 1), (716333897, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_53, prime_t37_149, prime_t37_1889, prime_lucas_716333897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126402 : Nat.totient 10685862914126402 = 5312047460201392 := by
  rw [← show ((([(2, 1), (173, 1), (30883996861637, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_173, prime_lucas_30883996861637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126403 : Nat.totient 10685862914126403 = 7101002150865800 := by
  rw [← show ((([(3, 1), (311, 1), (11453229275591, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_311, prime_lucas_11453229275591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126404 : Nat.totient 10685862914126404 = 5335448601266784 := by
  rw [← show ((([(2, 2), (1109, 1), (2003, 1), (1202644063, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_1109, prime_t37_2003, prime_lucas_1202644063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126405 : Nat.totient 10685862914126405 = 8544968655048448 := by
  rw [← show ((([(5, 1), (2297, 1), (930419060873, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_2297, prime_lucas_930419060873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126406 : Nat.totient 10685862914126406 = 3508790807623464 := by
  rw [← show ((([(2, 1), (3, 1), (67, 1), (26581748542603, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_67, prime_lucas_26581748542603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126407 : Nat.totient 10685862914126407 = 9159310593026712 := by
  rw [← show ((([(7, 1), (32730007, 1), (46640743, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_7, prime_t37_32730007, prime_lucas_46640743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126408 : Nat.totient 10685862914126408 = 5275760550230016 := by
  rw [← show ((([(2, 3), (83, 1), (2447, 1), (8317, 1), (790753, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_83, prime_t37_2447, prime_t37_8317, prime_t37_790753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126409 : Nat.totient 10685862914126409 = 7123908193057824 := by
  rw [← show ((([(3, 2), (30629789, 1), (38763509, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_30629789, prime_lucas_38763509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126410 : Nat.totient 10685862914126410 = 4255788373985280 := by
  rw [← show ((([(2, 1), (5, 1), (353, 1), (661, 1), (4579662077, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_353, prime_t37_661, prime_lucas_4579662077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126411 : Nat.totient 10685862914126411 = 9474285125620800 := by
  rw [← show ((([(11, 1), (41, 1), (2963, 1), (7996526947, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_11, prime_t37_41, prime_t37_2963, prime_lucas_7996526947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126412 : Nat.totient 10685862914126412 = 3528665012141008 := by
  rw [← show ((([(2, 2), (3, 1), (107, 1), (8322323141843, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_107, prime_lucas_8322323141843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126413 : Nat.totient 10685862914126413 = 9863869153584384 := by
  rw [← show ((([(13, 1), (2305753, 1), (356495017, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_13, prime_t37_2305753, prime_lucas_356495017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126414 : Nat.totient 10685862914126414 = 4579639814620824 := by
  rw [← show ((([(2, 1), (7, 1), (291359, 1), (2619709439, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_7, prime_t37_291359, prime_lucas_2619709439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126415 : Nat.totient 10685862914126415 = 5448150987319488 := by
  rw [← show ((([(3, 1), (5, 1), (43, 2), (47, 1), (8197540487, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_5, prime_t37_43, prime_t37_47, prime_lucas_8197540487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126416 : Nat.totient 10685862914126416 = 5342931457063200 := by
  rw [← show ((([(2, 4), (667866432132901, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_lucas_667866432132901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126417 : Nat.totient 10685862914126417 = 10056166135175232 := by
  rw [← show ((([(17, 1), (9007, 1), (69787961743, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_17, prime_t37_9007, prime_lucas_69787961743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126418 : Nat.totient 10685862914126418 = 3551174405775360 := by
  rw [← show ((([(2, 1), (3, 2), (769, 1), (1093, 1), (1231, 1), (573763, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_769, prime_t37_1093, prime_t37_1231, prime_t37_573763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126419 : Nat.totient 10685862914126419 = 10123449076540476 := by
  rw [← show ((([(19, 2), (29600728293979, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_19, prime_lucas_29600728293979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126420 : Nat.totient 10685862914126420 = 4258707289062912 := by
  rw [← show ((([(2, 2), (5, 1), (317, 1), (2437, 1), (13103, 1), (52783, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_317, prime_t37_2437, prime_t37_13103, prime_t37_52783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126421 : Nat.totient 10685862914126421 = 6096246192903744 := by
  rw [← show ((([(3, 1), (7, 1), (613, 1), (830098882477, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_7, prime_t37_613, prime_lucas_830098882477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126422 : Nat.totient 10685862914126422 = 4844741052465600 := by
  rw [← show ((([(2, 1), (11, 1), (439, 1), (3449, 1), (320796191, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_11, prime_t37_439, prime_t37_3449, prime_lucas_320796191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126423 : Nat.totient 10685862914126423 = 10217398727904984 := by
  rw [← show ((([(23, 1), (2647, 1), (175520489383, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_23, prime_t37_2647, prime_lucas_175520489383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126424 : Nat.totient 10685862914126424 = 3529381058304000 := by
  rw [← show ((([(2, 3), (3, 1), (193, 1), (251, 1), (9191096507, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_193, prime_t37_251, prime_lucas_9191096507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126425 : Nat.totient 10685862914126425 = 8505732088426320 := by
  rw [← show ((([(5, 2), (199, 1), (2147912143543, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_199, prime_lucas_2147912143543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126426 : Nat.totient 10685862914126426 = 4841864341434432 := by
  rw [← show ((([(2, 1), (13, 2), (59, 1), (983, 1), (3187, 1), (171043, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_13, prime_t37_59, prime_t37_983, prime_t37_3187, prime_t37_171043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126427 : Nat.totient 10685862914126427 = 7123306266378216 := by
  rw [← show ((([(3, 3), (11827, 1), (33463490363, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_11827, prime_lucas_33463490363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126428 : Nat.totient 10685862914126428 = 4579655534625528 := by
  rw [← show ((([(2, 2), (7, 2), (54519708745543, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_7, prime_lucas_54519708745543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126429 : Nat.totient 10685862914126429 = 10316450295971904 := by
  rw [← show ((([(29, 1), (12919, 1), (105467, 1), (270437, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_29, prime_t37_12919, prime_t37_105467, prime_t37_270437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126430 : Nat.totient 10685862914126430 = 2849545063819296 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (155047, 1), (2297338423, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_5, prime_t37_155047, prime_lucas_2297338423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126431 : Nat.totient 10685862914126431 = 10337779299492000 := by
  rw [← show ((([(31, 1), (3061, 1), (112611974941, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_31, prime_t37_3061, prime_lucas_112611974941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126432 : Nat.totient 10685862914126432 = 5342930785446400 := by
  rw [← show ((([(2, 5), (10665041, 1), (31311011, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_10665041, prime_t37_31311011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126433 : Nat.totient 10685862914126433 = 6476280554015800 := by
  rw [← show ((([(3, 1), (11, 2), (29437638881891, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_11, prime_lucas_29437638881891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126434 : Nat.totient 10685862914126434 = 5026987408101120 := by
  rw [← show ((([(2, 1), (17, 1), (4261, 1), (10627, 1), (6940783, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_17, prime_t37_4261, prime_t37_10627, prime_t37_6940783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126435 : Nat.totient 10685862914126435 = 7327444207813728 := by
  rw [← show ((([(5, 1), (7, 1), (1589663, 1), (192059807, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_7, prime_t37_1589663, prime_lucas_192059807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126436 : Nat.totient 10685862914126436 = 3559240145595456 := by
  rw [← show ((([(2, 2), (3, 2), (1429, 1), (16087, 1), (12912187, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_1429, prime_t37_16087, prime_t37_12912187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126437 : Nat.totient 10685862914126437 = 10395351169497792 := by
  rw [← show ((([(37, 1), (10243, 1), (15199, 1), (1855093, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_37, prime_t37_10243, prime_t37_15199, prime_t37_1855093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126438 : Nat.totient 10685862914126438 = 5058960079177800 := by
  rw [← show ((([(2, 1), (19, 1), (1831, 1), (153581058871, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_19, prime_t37_1831, prime_lucas_153581058871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126439 : Nat.totient 10685862914126439 = 6556944643701120 := by
  rw [← show ((([(3, 1), (13, 1), (347, 1), (384941, 1), (2051263, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_13, prime_t37_347, prime_t37_384941, prime_t37_2051263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126440 : Nat.totient 10685862914126440 = 4274343456509952 := by
  rw [← show ((([(2, 3), (5, 1), (2562337, 1), (104258953, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_2562337, prime_lucas_104258953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126441 : Nat.totient 10685862914126441 = 10685621168885892 := by
  rw [← show ((([(44203, 1), (241745196347, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_44203, prime_lucas_241745196347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126442 : Nat.totient 10685862914126442 = 3052837531153200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (11471, 1), (22179871631, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_7, prime_t37_11471, prime_lucas_22179871631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126443 : Nat.totient 10685862914126443 = 10580062291214200 := by
  rw [← show ((([(101, 1), (105800622912143, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_101, prime_lucas_105800622912143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126444 : Nat.totient 10685862914126444 = 4853763140526080 := by
  rw [← show ((([(2, 2), (11, 1), (1409, 1), (172363747889, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_11, prime_t37_1409, prime_lucas_172363747889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126445 : Nat.totient 10685862914126445 = 5699126887534080 := by
  rw [← show ((([(3, 2), (5, 1), (237463620313921, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_5, prime_lucas_237463620313921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126446 : Nat.totient 10685862914126446 = 5110481536734904 := by
  rw [← show ((([(2, 1), (23, 1), (34403, 1), (6752357867, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_23, prime_t37_34403, prime_lucas_6752357867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126447 : Nat.totient 10685862914126447 = 10565797038686736 := by
  rw [← show ((([(89, 1), (120065875439623, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_89, prime_lucas_120065875439623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126448 : Nat.totient 10685862914126448 = 3553942471016448 := by
  rw [← show ((([(2, 4), (3, 1), (449, 1), (45317, 1), (10941097, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_449, prime_t37_45317, prime_t37_10941097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126449 : Nat.totient 10685862914126449 = 9159273458573136 := by
  rw [← show ((([(7, 1), (243539, 1), (6268202813, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_7, prime_t37_243539, prime_lucas_6268202813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126450 : Nat.totient 10685862914126450 = 4184348449176000 := by
  rw [← show ((([(2, 1), (5, 2), (61, 2), (211, 1), (272205859, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_5, prime_t37_61, prime_t37_211, prime_lucas_272205859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126451 : Nat.totient 10685862914126451 = 6704855161804800 := by
  rw [← show ((([(3, 1), (17, 1), (209526723806401, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_3, prime_t37_17, prime_lucas_209526723806401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126452 : Nat.totient 10685862914126452 = 4745007269084160 := by
  rw [← show ((([(2, 2), (13, 1), (41, 1), (79, 1), (1279, 1), (2699, 1), (18379, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_13, prime_t37_41, prime_t37_79, prime_t37_1279, prime_t37_2699, prime_t37_18379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126453 : Nat.totient 10685862914126453 = 10685862681486828 := by
  rw [← show ((([(62986559, 1), (169653067, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_62986559, prime_lucas_169653067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126454 : Nat.totient 10685862914126454 = 3492263230709760 := by
  rw [← show ((([(2, 1), (3, 6), (53, 1), (2287, 1), (5441, 1), (11113, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_3, prime_t37_53, prime_t37_2287, prime_t37_5441, prime_t37_11113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126455 : Nat.totient 10685862914126455 = 7771536664819200 := by
  rw [← show ((([(5, 1), (11, 1), (194288416620481, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_5, prime_t37_11, prime_lucas_194288416620481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t37_10685862914126456 : Nat.totient 10685862914126456 = 4577838931814400 := by
  rw [← show ((([(2, 3), (7, 1), (2521, 1), (75691781281, 1)] : List FactorBlock).map factorBlockValue).prod) = 10685862914126456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t37_2, prime_t37_7, prime_t37_2521, prime_lucas_75691781281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twentieth finite diagonal certificate -/

theorem certifiedKill_diagonal_t37 :
    certifiedKill (periodLcm 37) (periodLcm 37) 56 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t37_5342931457063201, phi_t37_5342931457063202, phi_t37_5342931457063203, phi_t37_5342931457063204, phi_t37_5342931457063205, phi_t37_5342931457063206, phi_t37_5342931457063207, phi_t37_5342931457063208, phi_t37_5342931457063209, phi_t37_5342931457063210, phi_t37_5342931457063211, phi_t37_5342931457063212, phi_t37_5342931457063213, phi_t37_5342931457063214, phi_t37_5342931457063215, phi_t37_5342931457063216, phi_t37_5342931457063217, phi_t37_5342931457063218, phi_t37_5342931457063219, phi_t37_5342931457063220, phi_t37_5342931457063221, phi_t37_5342931457063222, phi_t37_5342931457063223, phi_t37_5342931457063224, phi_t37_5342931457063225, phi_t37_5342931457063226, phi_t37_5342931457063227, phi_t37_5342931457063228, phi_t37_5342931457063229, phi_t37_5342931457063230, phi_t37_5342931457063231, phi_t37_5342931457063232, phi_t37_5342931457063233, phi_t37_5342931457063234, phi_t37_5342931457063235, phi_t37_5342931457063236, phi_t37_5342931457063237, phi_t37_5342931457063238, phi_t37_5342931457063239, phi_t37_5342931457063240, phi_t37_5342931457063241, phi_t37_5342931457063242, phi_t37_5342931457063243, phi_t37_5342931457063244, phi_t37_5342931457063245, phi_t37_5342931457063246, phi_t37_5342931457063247, phi_t37_5342931457063248, phi_t37_5342931457063249, phi_t37_5342931457063250, phi_t37_5342931457063251, phi_t37_5342931457063252, phi_t37_5342931457063253, phi_t37_5342931457063254, phi_t37_5342931457063255, phi_t37_5342931457063256, phi_t37_10685862914126401, phi_t37_10685862914126402, phi_t37_10685862914126403, phi_t37_10685862914126404, phi_t37_10685862914126405, phi_t37_10685862914126406, phi_t37_10685862914126407, phi_t37_10685862914126408, phi_t37_10685862914126409, phi_t37_10685862914126410, phi_t37_10685862914126411, phi_t37_10685862914126412, phi_t37_10685862914126413, phi_t37_10685862914126414, phi_t37_10685862914126415, phi_t37_10685862914126416, phi_t37_10685862914126417, phi_t37_10685862914126418, phi_t37_10685862914126419, phi_t37_10685862914126420, phi_t37_10685862914126421, phi_t37_10685862914126422, phi_t37_10685862914126423, phi_t37_10685862914126424, phi_t37_10685862914126425, phi_t37_10685862914126426, phi_t37_10685862914126427, phi_t37_10685862914126428, phi_t37_10685862914126429, phi_t37_10685862914126430, phi_t37_10685862914126431, phi_t37_10685862914126432, phi_t37_10685862914126433, phi_t37_10685862914126434, phi_t37_10685862914126435, phi_t37_10685862914126436, phi_t37_10685862914126437, phi_t37_10685862914126438, phi_t37_10685862914126439, phi_t37_10685862914126440, phi_t37_10685862914126441, phi_t37_10685862914126442, phi_t37_10685862914126443, phi_t37_10685862914126444, phi_t37_10685862914126445, phi_t37_10685862914126446, phi_t37_10685862914126447, phi_t37_10685862914126448, phi_t37_10685862914126449, phi_t37_10685862914126450, phi_t37_10685862914126451, phi_t37_10685862914126452, phi_t37_10685862914126453, phi_t37_10685862914126454, phi_t37_10685862914126455, phi_t37_10685862914126456]

def diagonalPincerCertificateScalesThroughT37 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37]

def diagonalPincerKillDepthThroughT37 : ℕ → ℕ
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
  | _ => 0

/-- All 20 imported scales through t=37 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t37 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT37,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT37 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT37, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT37] using certifiedKill_diagonal_t37

#print axioms certifiedKill_diagonal_all_imported_through_t37

end TotientTailPeriodKiller
end Erdos249257
