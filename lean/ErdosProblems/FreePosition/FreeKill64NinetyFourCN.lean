import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyFourCNFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyFourCNFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyFourCNFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyFourCNFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyFourCNFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyFourCNFastPow a n * ninetyFourCNFastPow a n * a else ninetyFourCNFastPow a n * ninetyFourCNFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyFourCN_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyFourCN_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyFourCN_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyFourCN_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyFourCN_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyFourCN_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyFourCN_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyFourCN_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyFourCN_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyFourCN_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyFourCN_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyFourCN_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyFourCN_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyFourCN_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyFourCN_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyFourCN_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyFourCN_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyFourCN_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyFourCN_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyFourCN_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyFourCN_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyFourCN_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyFourCN_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyFourCN_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyFourCN_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyFourCN_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyFourCN_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyFourCN_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyFourCN_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyFourCN_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyFourCN_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetyFourCN_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyFourCN_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyFourCN_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetyFourCN_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyFourCN_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyFourCN_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetyFourCN_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyFourCN_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetyFourCN_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetyFourCN_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetyFourCN_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetyFourCN_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetyFourCN_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyFourCN_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyFourCN_199 : Nat.Prime 199 := by norm_num

private theorem prime_ninetyFourCN_211 : Nat.Prime 211 := by norm_num

private theorem prime_ninetyFourCN_227 : Nat.Prime 227 := by norm_num

private theorem prime_ninetyFourCN_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetyFourCN_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetyFourCN_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyFourCN_241 : Nat.Prime 241 := by norm_num

private theorem prime_ninetyFourCN_251 : Nat.Prime 251 := by norm_num

private theorem prime_ninetyFourCN_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetyFourCN_263 : Nat.Prime 263 := by norm_num

private theorem prime_ninetyFourCN_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetyFourCN_271 : Nat.Prime 271 := by norm_num

private theorem prime_ninetyFourCN_281 : Nat.Prime 281 := by norm_num

private theorem prime_ninetyFourCN_283 : Nat.Prime 283 := by norm_num

private theorem prime_ninetyFourCN_293 : Nat.Prime 293 := by norm_num

private theorem prime_ninetyFourCN_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetyFourCN_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetyFourCN_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetyFourCN_331 : Nat.Prime 331 := by norm_num

private theorem prime_ninetyFourCN_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyFourCN_349 : Nat.Prime 349 := by norm_num

private theorem prime_ninetyFourCN_367 : Nat.Prime 367 := by norm_num

private theorem prime_ninetyFourCN_373 : Nat.Prime 373 := by norm_num

private theorem prime_ninetyFourCN_419 : Nat.Prime 419 := by norm_num

private theorem prime_ninetyFourCN_431 : Nat.Prime 431 := by norm_num

private theorem prime_ninetyFourCN_439 : Nat.Prime 439 := by norm_num

private theorem prime_ninetyFourCN_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetyFourCN_457 : Nat.Prime 457 := by norm_num

private theorem prime_ninetyFourCN_479 : Nat.Prime 479 := by norm_num

private theorem prime_ninetyFourCN_487 : Nat.Prime 487 := by norm_num

private theorem prime_ninetyFourCN_491 : Nat.Prime 491 := by norm_num

private theorem prime_ninetyFourCN_499 : Nat.Prime 499 := by norm_num

private theorem prime_ninetyFourCN_509 : Nat.Prime 509 := by norm_num

private theorem prime_ninetyFourCN_569 : Nat.Prime 569 := by norm_num

private theorem prime_ninetyFourCN_571 : Nat.Prime 571 := by norm_num

private theorem prime_ninetyFourCN_587 : Nat.Prime 587 := by norm_num

private theorem prime_ninetyFourCN_607 : Nat.Prime 607 := by norm_num

private theorem prime_ninetyFourCN_631 : Nat.Prime 631 := by norm_num

private theorem prime_ninetyFourCN_659 : Nat.Prime 659 := by norm_num

private theorem prime_ninetyFourCN_677 : Nat.Prime 677 := by norm_num

private theorem prime_ninetyFourCN_683 : Nat.Prime 683 := by norm_num

private theorem prime_ninetyFourCN_691 : Nat.Prime 691 := by norm_num

private theorem prime_ninetyFourCN_701 : Nat.Prime 701 := by norm_num

private theorem prime_ninetyFourCN_709 : Nat.Prime 709 := by norm_num

private theorem prime_ninetyFourCN_733 : Nat.Prime 733 := by norm_num

private theorem prime_ninetyFourCN_751 : Nat.Prime 751 := by norm_num

private theorem prime_ninetyFourCN_757 : Nat.Prime 757 := by norm_num

private theorem prime_ninetyFourCN_761 : Nat.Prime 761 := by norm_num

private theorem prime_ninetyFourCN_797 : Nat.Prime 797 := by norm_num

private theorem prime_ninetyFourCN_809 : Nat.Prime 809 := by norm_num

private theorem prime_ninetyFourCN_829 : Nat.Prime 829 := by norm_num

private theorem prime_ninetyFourCN_863 : Nat.Prime 863 := by norm_num

private theorem prime_ninetyFourCN_883 : Nat.Prime 883 := by norm_num

private theorem prime_ninetyFourCN_911 : Nat.Prime 911 := by norm_num

private theorem prime_ninetyFourCN_929 : Nat.Prime 929 := by norm_num

private theorem prime_ninetyFourCN_941 : Nat.Prime 941 := by norm_num

private theorem prime_ninetyFourCN_947 : Nat.Prime 947 := by norm_num

private theorem prime_ninetyFourCN_953 : Nat.Prime 953 := by norm_num

private theorem prime_ninetyFourCN_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_ninetyFourCN_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_ninetyFourCN_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_ninetyFourCN_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_ninetyFourCN_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_ninetyFourCN_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_ninetyFourCN_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_ninetyFourCN_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_ninetyFourCN_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_ninetyFourCN_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_ninetyFourCN_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_ninetyFourCN_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_ninetyFourCN_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_ninetyFourCN_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_ninetyFourCN_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_ninetyFourCN_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_ninetyFourCN_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_ninetyFourCN_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_ninetyFourCN_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_ninetyFourCN_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_ninetyFourCN_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_ninetyFourCN_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_ninetyFourCN_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_ninetyFourCN_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_ninetyFourCN_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_ninetyFourCN_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_ninetyFourCN_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_ninetyFourCN_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_ninetyFourCN_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_ninetyFourCN_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_ninetyFourCN_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_ninetyFourCN_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_ninetyFourCN_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_ninetyFourCN_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_ninetyFourCN_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_ninetyFourCN_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_ninetyFourCN_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_ninetyFourCN_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_ninetyFourCN_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_ninetyFourCN_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_ninetyFourCN_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_ninetyFourCN_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_ninetyFourCN_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_ninetyFourCN_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_ninetyFourCN_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_ninetyFourCN_2557 : Nat.Prime 2557 := by norm_num

private theorem prime_ninetyFourCN_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_ninetyFourCN_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_ninetyFourCN_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_ninetyFourCN_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_ninetyFourCN_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_ninetyFourCN_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_ninetyFourCN_3023 : Nat.Prime 3023 := by norm_num

private theorem prime_ninetyFourCN_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_ninetyFourCN_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_ninetyFourCN_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_ninetyFourCN_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_ninetyFourCN_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_ninetyFourCN_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_ninetyFourCN_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_ninetyFourCN_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_ninetyFourCN_3797 : Nat.Prime 3797 := by norm_num

private theorem prime_ninetyFourCN_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_ninetyFourCN_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_ninetyFourCN_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_ninetyFourCN_4261 : Nat.Prime 4261 := by norm_num

private theorem prime_ninetyFourCN_4271 : Nat.Prime 4271 := by norm_num

private theorem prime_ninetyFourCN_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_ninetyFourCN_4657 : Nat.Prime 4657 := by norm_num

private theorem prime_ninetyFourCN_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_ninetyFourCN_5023 : Nat.Prime 5023 := by norm_num

private theorem prime_ninetyFourCN_5039 : Nat.Prime 5039 := by norm_num

private theorem prime_ninetyFourCN_5197 : Nat.Prime 5197 := by norm_num

private theorem prime_ninetyFourCN_5279 : Nat.Prime 5279 := by norm_num

private theorem prime_ninetyFourCN_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_ninetyFourCN_5441 : Nat.Prime 5441 := by norm_num

private theorem prime_ninetyFourCN_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_ninetyFourCN_5717 : Nat.Prime 5717 := by norm_num

private theorem prime_ninetyFourCN_5737 : Nat.Prime 5737 := by norm_num

private theorem prime_ninetyFourCN_5861 : Nat.Prime 5861 := by norm_num

private theorem prime_ninetyFourCN_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_ninetyFourCN_6053 : Nat.Prime 6053 := by norm_num

private theorem prime_ninetyFourCN_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_ninetyFourCN_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_ninetyFourCN_6337 : Nat.Prime 6337 := by norm_num

private theorem prime_ninetyFourCN_6529 : Nat.Prime 6529 := by norm_num

private theorem prime_ninetyFourCN_6569 : Nat.Prime 6569 := by norm_num

private theorem prime_ninetyFourCN_6679 : Nat.Prime 6679 := by norm_num

private theorem prime_ninetyFourCN_6857 : Nat.Prime 6857 := by norm_num

private theorem prime_ninetyFourCN_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_ninetyFourCN_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_ninetyFourCN_7219 : Nat.Prime 7219 := by norm_num

private theorem prime_ninetyFourCN_8467 : Nat.Prime 8467 := by norm_num

private theorem prime_ninetyFourCN_8629 : Nat.Prime 8629 := by norm_num

private theorem prime_ninetyFourCN_8923 : Nat.Prime 8923 := by norm_num

private theorem prime_ninetyFourCN_9967 : Nat.Prime 9967 := by norm_num

private theorem prime_ninetyFourCN_10501 : Nat.Prime 10501 := by norm_num

private theorem prime_ninetyFourCN_11117 : Nat.Prime 11117 := by norm_num

private theorem prime_ninetyFourCN_11969 : Nat.Prime 11969 := by norm_num

private theorem prime_ninetyFourCN_12479 : Nat.Prime 12479 := by norm_num

private theorem prime_ninetyFourCN_12979 : Nat.Prime 12979 := by norm_num

private theorem prime_ninetyFourCN_13499 : Nat.Prime 13499 := by norm_num

private theorem prime_ninetyFourCN_13553 : Nat.Prime 13553 := by norm_num

private theorem prime_ninetyFourCN_13687 : Nat.Prime 13687 := by norm_num

private theorem prime_ninetyFourCN_13711 : Nat.Prime 13711 := by norm_num

private theorem prime_ninetyFourCN_14149 : Nat.Prime 14149 := by norm_num

private theorem prime_ninetyFourCN_14519 : Nat.Prime 14519 := by norm_num

private theorem prime_ninetyFourCN_14533 : Nat.Prime 14533 := by norm_num

private theorem prime_ninetyFourCN_14821 : Nat.Prime 14821 := by norm_num

private theorem prime_ninetyFourCN_14923 : Nat.Prime 14923 := by norm_num

private theorem prime_ninetyFourCN_15013 : Nat.Prime 15013 := by norm_num

private theorem prime_ninetyFourCN_15107 : Nat.Prime 15107 := by norm_num

private theorem prime_ninetyFourCN_15289 : Nat.Prime 15289 := by norm_num

private theorem prime_ninetyFourCN_15319 : Nat.Prime 15319 := by norm_num

private theorem prime_ninetyFourCN_16651 : Nat.Prime 16651 := by norm_num

private theorem prime_ninetyFourCN_16693 : Nat.Prime 16693 := by norm_num

private theorem prime_ninetyFourCN_16927 : Nat.Prime 16927 := by norm_num

private theorem prime_ninetyFourCN_17729 : Nat.Prime 17729 := by norm_num

private theorem prime_ninetyFourCN_18251 : Nat.Prime 18251 := by norm_num

private theorem prime_ninetyFourCN_19079 : Nat.Prime 19079 := by norm_num

private theorem prime_ninetyFourCN_19087 : Nat.Prime 19087 := by norm_num

private theorem prime_ninetyFourCN_20287 : Nat.Prime 20287 := by norm_num

private theorem prime_ninetyFourCN_21817 : Nat.Prime 21817 := by norm_num

private theorem prime_ninetyFourCN_22543 : Nat.Prime 22543 := by norm_num

private theorem prime_ninetyFourCN_23099 : Nat.Prime 23099 := by norm_num

private theorem prime_ninetyFourCN_23333 : Nat.Prime 23333 := by norm_num

private theorem prime_ninetyFourCN_25301 : Nat.Prime 25301 := by norm_num

private theorem prime_ninetyFourCN_25577 : Nat.Prime 25577 := by norm_num

private theorem prime_ninetyFourCN_26423 : Nat.Prime 26423 := by norm_num

private theorem prime_ninetyFourCN_26959 : Nat.Prime 26959 := by norm_num

private theorem prime_ninetyFourCN_27059 : Nat.Prime 27059 := by norm_num

private theorem prime_ninetyFourCN_27791 : Nat.Prime 27791 := by norm_num

private theorem prime_ninetyFourCN_28181 : Nat.Prime 28181 := by norm_num

private theorem prime_ninetyFourCN_28627 : Nat.Prime 28627 := by norm_num

private theorem prime_ninetyFourCN_29201 : Nat.Prime 29201 := by norm_num

private theorem prime_ninetyFourCN_30097 : Nat.Prime 30097 := by norm_num

private theorem prime_ninetyFourCN_30181 : Nat.Prime 30181 := by norm_num

private theorem prime_ninetyFourCN_30241 : Nat.Prime 30241 := by norm_num

private theorem prime_ninetyFourCN_31159 : Nat.Prime 31159 := by norm_num

private theorem prime_ninetyFourCN_32063 : Nat.Prime 32063 := by norm_num

private theorem prime_ninetyFourCN_32309 : Nat.Prime 32309 := by norm_num

private theorem prime_ninetyFourCN_36191 : Nat.Prime 36191 := by norm_num

private theorem prime_ninetyFourCN_36607 : Nat.Prime 36607 := by norm_num

private theorem prime_ninetyFourCN_36821 : Nat.Prime 36821 := by norm_num

private theorem prime_ninetyFourCN_37579 : Nat.Prime 37579 := by norm_num

private theorem prime_ninetyFourCN_40283 : Nat.Prime 40283 := by norm_num

private theorem prime_ninetyFourCN_40961 : Nat.Prime 40961 := by norm_num

private theorem prime_ninetyFourCN_41183 : Nat.Prime 41183 := by norm_num

private theorem prime_ninetyFourCN_41617 : Nat.Prime 41617 := by norm_num

private theorem prime_ninetyFourCN_41777 : Nat.Prime 41777 := by norm_num

private theorem prime_ninetyFourCN_42407 : Nat.Prime 42407 := by norm_num

private theorem prime_ninetyFourCN_43717 : Nat.Prime 43717 := by norm_num

private theorem prime_ninetyFourCN_45077 : Nat.Prime 45077 := by norm_num

private theorem prime_ninetyFourCN_45677 : Nat.Prime 45677 := by norm_num

private theorem prime_ninetyFourCN_46589 : Nat.Prime 46589 := by norm_num

private theorem prime_ninetyFourCN_49697 : Nat.Prime 49697 := by norm_num

private theorem prime_ninetyFourCN_54011 : Nat.Prime 54011 := by norm_num

private theorem prime_ninetyFourCN_54799 : Nat.Prime 54799 := by norm_num

private theorem prime_ninetyFourCN_58979 : Nat.Prime 58979 := by norm_num

private theorem prime_ninetyFourCN_59167 : Nat.Prime 59167 := by norm_num

private theorem prime_ninetyFourCN_62627 : Nat.Prime 62627 := by norm_num

private theorem prime_ninetyFourCN_67189 : Nat.Prime 67189 := by norm_num

private theorem prime_ninetyFourCN_71453 : Nat.Prime 71453 := by norm_num

private theorem prime_ninetyFourCN_71741 : Nat.Prime 71741 := by norm_num

private theorem prime_ninetyFourCN_73141 : Nat.Prime 73141 := by norm_num

private theorem prime_ninetyFourCN_73673 : Nat.Prime 73673 := by norm_num

private theorem prime_ninetyFourCN_75277 : Nat.Prime 75277 := by norm_num

private theorem prime_ninetyFourCN_81509 : Nat.Prime 81509 := by norm_num

private theorem prime_ninetyFourCN_91243 : Nat.Prime 91243 := by norm_num

private theorem prime_ninetyFourCN_94447 : Nat.Prime 94447 := by norm_num

private theorem prime_ninetyFourCN_94573 : Nat.Prime 94573 := by norm_num

private theorem prime_ninetyFourCN_98323 : Nat.Prime 98323 := by norm_num

private theorem prime_ninetyFourCN_102673 : Nat.Prime 102673 := by norm_num

private theorem prime_ninetyFourCN_103483 : Nat.Prime 103483 := by norm_num

private theorem prime_ninetyFourCN_104987 : Nat.Prime 104987 := by norm_num

private theorem prime_ninetyFourCN_124541 : Nat.Prime 124541 := by norm_num

private theorem prime_ninetyFourCN_127277 : Nat.Prime 127277 := by norm_num

private theorem prime_ninetyFourCN_127321 : Nat.Prime 127321 := by norm_num

private theorem prime_ninetyFourCN_130517 : Nat.Prime 130517 := by norm_num

private theorem prime_ninetyFourCN_140057 : Nat.Prime 140057 := by norm_num

private theorem prime_ninetyFourCN_143243 : Nat.Prime 143243 := by norm_num

private theorem prime_ninetyFourCN_143947 : Nat.Prime 143947 := by norm_num

private theorem prime_ninetyFourCN_149341 : Nat.Prime 149341 := by norm_num

private theorem prime_ninetyFourCN_168347 : Nat.Prime 168347 := by norm_num

private theorem prime_ninetyFourCN_173923 : Nat.Prime 173923 := by norm_num

private theorem prime_ninetyFourCN_174679 : Nat.Prime 174679 := by norm_num

private theorem prime_ninetyFourCN_177173 : Nat.Prime 177173 := by norm_num

private theorem prime_ninetyFourCN_178561 : Nat.Prime 178561 := by norm_num

private theorem prime_ninetyFourCN_184753 : Nat.Prime 184753 := by norm_num

private theorem prime_ninetyFourCN_187871 : Nat.Prime 187871 := by norm_num

private theorem prime_ninetyFourCN_187909 : Nat.Prime 187909 := by norm_num

private theorem prime_ninetyFourCN_192737 : Nat.Prime 192737 := by norm_num

private theorem prime_ninetyFourCN_193379 : Nat.Prime 193379 := by norm_num

private theorem prime_ninetyFourCN_207967 : Nat.Prime 207967 := by norm_num

private theorem prime_ninetyFourCN_210139 : Nat.Prime 210139 := by norm_num

private theorem prime_ninetyFourCN_211313 : Nat.Prime 211313 := by norm_num

private theorem prime_ninetyFourCN_211747 : Nat.Prime 211747 := by norm_num

private theorem prime_ninetyFourCN_212183 : Nat.Prime 212183 := by norm_num

private theorem prime_ninetyFourCN_213887 : Nat.Prime 213887 := by norm_num

private theorem prime_ninetyFourCN_262877 : Nat.Prime 262877 := by norm_num

private theorem prime_ninetyFourCN_271619 : Nat.Prime 271619 := by norm_num

private theorem prime_ninetyFourCN_292427 : Nat.Prime 292427 := by norm_num

private theorem prime_ninetyFourCN_294887 : Nat.Prime 294887 := by norm_num

private theorem prime_ninetyFourCN_308849 : Nat.Prime 308849 := by norm_num

private theorem prime_ninetyFourCN_324757 : Nat.Prime 324757 := by norm_num

private theorem prime_ninetyFourCN_332951 : Nat.Prime 332951 := by norm_num

private theorem prime_ninetyFourCN_336767 : Nat.Prime 336767 := by norm_num

private theorem prime_ninetyFourCN_356933 : Nat.Prime 356933 := by norm_num

private theorem prime_ninetyFourCN_397211 : Nat.Prime 397211 := by norm_num

private theorem prime_ninetyFourCN_404849 : Nat.Prime 404849 := by norm_num

private theorem prime_ninetyFourCN_413779 : Nat.Prime 413779 := by norm_num

private theorem prime_ninetyFourCN_418871 : Nat.Prime 418871 := by norm_num

private theorem prime_ninetyFourCN_422231 : Nat.Prime 422231 := by norm_num

private theorem prime_ninetyFourCN_445799 : Nat.Prime 445799 := by norm_num

private theorem prime_ninetyFourCN_456167 : Nat.Prime 456167 := by norm_num

private theorem prime_ninetyFourCN_459763 : Nat.Prime 459763 := by norm_num

private theorem prime_ninetyFourCN_496163 : Nat.Prime 496163 := by norm_num

private theorem prime_ninetyFourCN_510049 : Nat.Prime 510049 := by norm_num

private theorem prime_ninetyFourCN_520649 : Nat.Prime 520649 := by norm_num

private theorem prime_ninetyFourCN_573163 : Nat.Prime 573163 := by norm_num

private theorem prime_ninetyFourCN_584777 : Nat.Prime 584777 := by norm_num

private theorem prime_ninetyFourCN_615941 : Nat.Prime 615941 := by norm_num

private theorem prime_ninetyFourCN_643691 : Nat.Prime 643691 := by norm_num

private theorem prime_ninetyFourCN_650483 : Nat.Prime 650483 := by norm_num

private theorem prime_ninetyFourCN_651221 : Nat.Prime 651221 := by norm_num

private theorem prime_ninetyFourCN_652903 : Nat.Prime 652903 := by norm_num

private theorem prime_ninetyFourCN_653339 : Nat.Prime 653339 := by norm_num

private theorem prime_ninetyFourCN_680503 : Nat.Prime 680503 := by norm_num

private theorem prime_ninetyFourCN_702991 : Nat.Prime 702991 := by norm_num

private theorem prime_ninetyFourCN_760549 : Nat.Prime 760549 := by norm_num

private theorem prime_ninetyFourCN_1021303 : Nat.Prime 1021303 := by norm_num

private theorem prime_ninetyFourCN_1025509 : Nat.Prime 1025509 := by norm_num

private theorem prime_ninetyFourCN_1028003 : Nat.Prime 1028003 := by norm_num

private theorem prime_ninetyFourCN_1129561 : Nat.Prime 1129561 := by norm_num

private theorem prime_ninetyFourCN_1166779 : Nat.Prime 1166779 := by norm_num

private theorem prime_ninetyFourCN_1226857 : Nat.Prime 1226857 := by norm_num

private theorem prime_ninetyFourCN_1246543 : Nat.Prime 1246543 := by norm_num

private theorem prime_ninetyFourCN_1294201 : Nat.Prime 1294201 := by norm_num

private theorem prime_ninetyFourCN_1372843 : Nat.Prime 1372843 := by norm_num

private theorem prime_ninetyFourCN_1445419 : Nat.Prime 1445419 := by norm_num

private theorem prime_ninetyFourCN_1518571 : Nat.Prime 1518571 := by norm_num

private theorem prime_ninetyFourCN_1594261 : Nat.Prime 1594261 := by norm_num

private theorem prime_ninetyFourCN_1639699 : Nat.Prime 1639699 := by norm_num

private theorem prime_ninetyFourCN_1813391 : Nat.Prime 1813391 := by norm_num

private theorem prime_ninetyFourCN_1862429 : Nat.Prime 1862429 := by norm_num

private theorem prime_ninetyFourCN_1890541 : Nat.Prime 1890541 := by norm_num

private theorem prime_ninetyFourCN_1959253 : Nat.Prime 1959253 := by norm_num

private theorem prime_ninetyFourCN_2017121 : Nat.Prime 2017121 := by norm_num

private theorem prime_ninetyFourCN_2070533 : Nat.Prime 2070533 := by norm_num

private theorem prime_ninetyFourCN_2179049 : Nat.Prime 2179049 := by norm_num

private theorem prime_ninetyFourCN_2185357 : Nat.Prime 2185357 := by norm_num

private theorem prime_ninetyFourCN_2334307 : Nat.Prime 2334307 := by norm_num

private theorem prime_ninetyFourCN_2352043 : Nat.Prime 2352043 := by norm_num

private theorem prime_ninetyFourCN_2582609 : Nat.Prime 2582609 := by norm_num

private theorem prime_ninetyFourCN_2620439 : Nat.Prime 2620439 := by norm_num

private theorem prime_ninetyFourCN_3243007 : Nat.Prime 3243007 := by norm_num

private theorem prime_ninetyFourCN_3251447 : Nat.Prime 3251447 := by norm_num

private theorem prime_ninetyFourCN_3433007 : Nat.Prime 3433007 := by norm_num

private theorem prime_ninetyFourCN_3478763 : Nat.Prime 3478763 := by norm_num

private theorem prime_ninetyFourCN_3647431 : Nat.Prime 3647431 := by norm_num

private theorem prime_ninetyFourCN_3908837 : Nat.Prime 3908837 := by norm_num

private theorem prime_ninetyFourCN_3938771 : Nat.Prime 3938771 := by norm_num

private theorem prime_ninetyFourCN_4182043 : Nat.Prime 4182043 := by norm_num

private theorem prime_ninetyFourCN_4189019 : Nat.Prime 4189019 := by norm_num

private theorem prime_ninetyFourCN_4245079 : Nat.Prime 4245079 := by norm_num

private theorem prime_ninetyFourCN_4356997 : Nat.Prime 4356997 := by norm_num

private theorem prime_ninetyFourCN_4414219 : Nat.Prime 4414219 := by norm_num

private theorem prime_ninetyFourCN_4507043 : Nat.Prime 4507043 := by norm_num

private theorem prime_ninetyFourCN_4690949 : Nat.Prime 4690949 := by norm_num

private theorem prime_ninetyFourCN_4974239 : Nat.Prime 4974239 := by norm_num

private theorem prime_ninetyFourCN_5077283 : Nat.Prime 5077283 := by norm_num

private theorem prime_ninetyFourCN_5089769 : Nat.Prime 5089769 := by norm_num

private theorem prime_ninetyFourCN_5759543 : Nat.Prime 5759543 := by norm_num

private theorem prime_ninetyFourCN_5916511 : Nat.Prime 5916511 := by norm_num

private theorem prime_ninetyFourCN_6450427 : Nat.Prime 6450427 := by norm_num

private theorem prime_ninetyFourCN_6477161 : Nat.Prime 6477161 := by norm_num

private theorem prime_ninetyFourCN_6819781 : Nat.Prime 6819781 := by norm_num

private theorem prime_ninetyFourCN_7500397 : Nat.Prime 7500397 := by norm_num

private theorem prime_ninetyFourCN_8000819 : Nat.Prime 8000819 := by norm_num

private theorem prime_ninetyFourCN_8074567 : Nat.Prime 8074567 := by norm_num

private theorem prime_ninetyFourCN_8119369 : Nat.Prime 8119369 := by norm_num

private theorem prime_ninetyFourCN_8271847 : Nat.Prime 8271847 := by norm_num

private theorem prime_ninetyFourCN_8543279 : Nat.Prime 8543279 := by norm_num

private theorem prime_ninetyFourCN_9235781 : Nat.Prime 9235781 := by norm_num

private theorem prime_ninetyFourCN_9393323 : Nat.Prime 9393323 := by norm_num

private theorem prime_ninetyFourCN_9468449 : Nat.Prime 9468449 := by norm_num

private theorem prime_ninetyFourCN_9654247 : Nat.Prime 9654247 := by norm_num

private theorem prime_ninetyFourCN_10309807 : Nat.Prime 10309807 := by norm_num

private theorem prime_ninetyFourCN_10699153 : Nat.Prime 10699153 := by norm_num

private theorem prime_ninetyFourCN_11085209 : Nat.Prime 11085209 := by norm_num

private theorem prime_ninetyFourCN_11148133 : Nat.Prime 11148133 := by norm_num

private theorem prime_ninetyFourCN_11443931 : Nat.Prime 11443931 := by norm_num

private theorem prime_ninetyFourCN_11699447 : Nat.Prime 11699447 := by norm_num

private theorem prime_ninetyFourCN_12376249 : Nat.Prime 12376249 := by norm_num

private theorem prime_ninetyFourCN_12625027 : Nat.Prime 12625027 := by norm_num

private theorem prime_ninetyFourCN_13024021 : Nat.Prime 13024021 := by norm_num

private theorem prime_ninetyFourCN_13108583 : Nat.Prime 13108583 := by norm_num

private theorem prime_ninetyFourCN_13705589 : Nat.Prime 13705589 := by norm_num

private theorem prime_ninetyFourCN_13878391 : Nat.Prime 13878391 := by norm_num

private theorem prime_ninetyFourCN_13926889 : Nat.Prime 13926889 := by norm_num

private theorem prime_ninetyFourCN_13941247 : Nat.Prime 13941247 := by norm_num

private theorem prime_ninetyFourCN_14460079 : Nat.Prime 14460079 := by norm_num

private theorem prime_ninetyFourCN_14623751 : Nat.Prime 14623751 := by norm_num

private theorem prime_ninetyFourCN_15492173 : Nat.Prime 15492173 := by norm_num

private theorem prime_ninetyFourCN_16089109 : Nat.Prime 16089109 := by norm_num

private theorem prime_ninetyFourCN_16853933 : Nat.Prime 16853933 := by norm_num

private theorem prime_ninetyFourCN_17057531 : Nat.Prime 17057531 := by norm_num

private theorem prime_ninetyFourCN_17438857 : Nat.Prime 17438857 := by norm_num

private theorem prime_ninetyFourCN_17753179 : Nat.Prime 17753179 := by norm_num

private theorem prime_ninetyFourCN_17919943 : Nat.Prime 17919943 := by norm_num

private theorem prime_ninetyFourCN_20698507 : Nat.Prime 20698507 := by norm_num

private theorem prime_ninetyFourCN_21831833 : Nat.Prime 21831833 := by norm_num

private theorem prime_ninetyFourCN_22049683 : Nat.Prime 22049683 := by norm_num

private theorem prime_ninetyFourCN_22841563 : Nat.Prime 22841563 := by norm_num

private theorem prime_ninetyFourCN_23937451 : Nat.Prime 23937451 := by norm_num

private theorem prime_ninetyFourCN_25211161 : Nat.Prime 25211161 := by norm_num

private theorem prime_ninetyFourCN_26204989 : Nat.Prime 26204989 := by norm_num

private theorem prime_ninetyFourCN_28529971 : Nat.Prime 28529971 := by norm_num

private theorem prime_ninetyFourCN_32530543 : Nat.Prime 32530543 := by
  apply lucas_primality 32530543 (3 : ZMod 32530543)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (127, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (127, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) = 32530543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_127
      · exact prime_ninetyFourCN_3881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32530543) ^ 16265271 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32530543) ^ 10843514 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32530543) ^ 2957322 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32530543) ^ 256146 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32530543) ^ 8382 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_33707867 : Nat.Prime 33707867 := by
  apply lucas_primality 33707867 (2 : ZMod 33707867)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16853933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16853933, 1)] : List FactorBlock).map factorBlockValue).prod) = 33707867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_16853933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33707867) ^ 16853933 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 33707867) ^ 2 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_33761641 : Nat.Prime 33761641 := by
  apply lucas_primality 33761641 (46 : ZMod 33761641)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (25577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (25577, 1)] : List FactorBlock).map factorBlockValue).prod) = 33761641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_25577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (46 : ZMod 33761641) ^ 16880820 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (46 : ZMod 33761641) ^ 11253880 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (46 : ZMod 33761641) ^ 6752328 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (46 : ZMod 33761641) ^ 3069240 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (46 : ZMod 33761641) ^ 1320 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_42299813 : Nat.Prime 42299813 := by
  apply lucas_primality 42299813 (2 : ZMod 42299813)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (71, 1), (3169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (71, 1), (3169, 1)] : List FactorBlock).map factorBlockValue).prod) = 42299813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_47
      · exact prime_ninetyFourCN_71
      · exact prime_ninetyFourCN_3169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42299813) ^ 21149906 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42299813) ^ 899996 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42299813) ^ 595772 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 42299813) ^ 13348 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_42533999 : Nat.Prime 42533999 := by
  apply lucas_primality 42533999 (7 : ZMod 42533999)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (107, 1), (15289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (107, 1), (15289, 1)] : List FactorBlock).map factorBlockValue).prod) = 42533999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_107
      · exact prime_ninetyFourCN_15289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42533999) ^ 21266999 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 42533999) ^ 3271846 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 42533999) ^ 397514 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 42533999) ^ 2782 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_44394499 : Nat.Prime 44394499 := by
  apply lucas_primality 44394499 (3 : ZMod 44394499)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (941, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (941, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) = 44394499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_941
      · exact prime_ninetyFourCN_2621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44394499) ^ 22197249 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 44394499) ^ 14798166 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 44394499) ^ 47178 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 44394499) ^ 16938 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_48525041 : Nat.Prime 48525041 := by
  apply lucas_primality 48525041 (6 : ZMod 48525041)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (197, 1), (3079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (197, 1), (3079, 1)] : List FactorBlock).map factorBlockValue).prod) = 48525041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_197
      · exact prime_ninetyFourCN_3079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 48525041) ^ 24262520 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 48525041) ^ 9705008 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 48525041) ^ 246320 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 48525041) ^ 15760 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_49319531 : Nat.Prime 49319531 := by
  apply lucas_primality 49319531 (2 : ZMod 49319531)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (73, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (73, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) = 49319531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_5197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49319531) ^ 24659765 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 49319531) ^ 9863906 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 49319531) ^ 3793810 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 49319531) ^ 675610 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 49319531) ^ 9490 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_50424221 : Nat.Prime 50424221 := by
  apply lucas_primality 50424221 (2 : ZMod 50424221)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (137, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (137, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 50424221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_137
      · exact prime_ninetyFourCN_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50424221) ^ 25212110 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 50424221) ^ 10084844 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 50424221) ^ 7203460 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 50424221) ^ 4584020 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 50424221) ^ 368060 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 50424221) ^ 210980 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_51512837 : Nat.Prime 51512837 := by
  apply lucas_primality 51512837 (2 : ZMod 51512837)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (509, 1), (25301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (509, 1), (25301, 1)] : List FactorBlock).map factorBlockValue).prod) = 51512837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_509
      · exact prime_ninetyFourCN_25301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51512837) ^ 25756418 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 51512837) ^ 101204 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 51512837) ^ 2036 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_54628649 : Nat.Prime 54628649 := by
  apply lucas_primality 54628649 (3 : ZMod 54628649)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (281, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (281, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 54628649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_281
      · exact prime_ninetyFourCN_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54628649) ^ 27314324 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 54628649) ^ 2875192 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 54628649) ^ 194408 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 54628649) ^ 42712 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_55900667 : Nat.Prime 55900667 := by
  apply lucas_primality 55900667 (2 : ZMod 55900667)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (239, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (239, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) = 55900667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_83
      · exact prime_ninetyFourCN_239
      · exact prime_ninetyFourCN_1409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55900667) ^ 27950333 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 55900667) ^ 673502 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 55900667) ^ 233894 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 55900667) ^ 39674 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_56916319 : Nat.Prime 56916319 := by
  apply lucas_primality 56916319 (3 : ZMod 56916319)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1613, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1613, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) = 56916319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_1613
      · exact prime_ninetyFourCN_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56916319) ^ 28458159 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 56916319) ^ 18972106 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 56916319) ^ 35286 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 56916319) ^ 9678 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_60743909 : Nat.Prime 60743909 := by
  apply lucas_primality 60743909 (2 : ZMod 60743909)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (213887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (213887, 1)] : List FactorBlock).map factorBlockValue).prod) = 60743909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_71
      · exact prime_ninetyFourCN_213887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60743909) ^ 30371954 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60743909) ^ 855548 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60743909) ^ 284 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_61858843 : Nat.Prime 61858843 := by
  apply lucas_primality 61858843 (2 : ZMod 61858843)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10309807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10309807, 1)] : List FactorBlock).map factorBlockValue).prod) = 61858843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_10309807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61858843) ^ 30929421 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 61858843) ^ 20619614 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 61858843) ^ 6 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_66888799 : Nat.Prime 66888799 := by
  apply lucas_primality 66888799 (6 : ZMod 66888799)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11148133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11148133, 1)] : List FactorBlock).map factorBlockValue).prod) = 66888799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11148133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 66888799) ^ 33444399 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 66888799) ^ 22296266 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 66888799) ^ 6 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_70359067 : Nat.Prime 70359067 := by
  apply lucas_primality 70359067 (5 : ZMod 70359067)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3908837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3908837, 1)] : List FactorBlock).map factorBlockValue).prod) = 70359067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_3908837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 70359067) ^ 35179533 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 70359067) ^ 23453022 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 70359067) ^ 18 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_101946809 : Nat.Prime 101946809 := by
  apply lucas_primality 101946809 (3 : ZMod 101946809)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (59, 1), (5023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (59, 1), (5023, 1)] : List FactorBlock).map factorBlockValue).prod) = 101946809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_43
      · exact prime_ninetyFourCN_59
      · exact prime_ninetyFourCN_5023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101946809) ^ 50973404 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 101946809) ^ 2370856 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 101946809) ^ 1727912 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 101946809) ^ 20296 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_105629011 : Nat.Prime 105629011 := by
  apply lucas_primality 105629011 (2 : ZMod 105629011)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (113, 1), (31159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (113, 1), (31159, 1)] : List FactorBlock).map factorBlockValue).prod) = 105629011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_113
      · exact prime_ninetyFourCN_31159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105629011) ^ 52814505 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 105629011) ^ 35209670 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 105629011) ^ 21125802 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 105629011) ^ 934770 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 105629011) ^ 3390 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_106202309 : Nat.Prime 106202309 := by
  apply lucas_primality 106202309 (2 : ZMod 106202309)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (262877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (262877, 1)] : List FactorBlock).map factorBlockValue).prod) = 106202309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_101
      · exact prime_ninetyFourCN_262877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106202309) ^ 53101154 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 106202309) ^ 1051508 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 106202309) ^ 404 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_108050659 : Nat.Prime 108050659 := by
  apply lucas_primality 108050659 (2 : ZMod 108050659)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (73, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (73, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) = 108050659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_43
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_5737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108050659) ^ 54025329 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 108050659) ^ 36016886 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 108050659) ^ 2512806 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 108050659) ^ 1480146 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 108050659) ^ 18834 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_110262239 : Nat.Prime 110262239 := by
  apply lucas_primality 110262239 (23 : ZMod 110262239)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3243007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3243007, 1)] : List FactorBlock).map factorBlockValue).prod) = 110262239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_3243007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 110262239) ^ 55131119 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (23 : ZMod 110262239) ^ 6486014 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (23 : ZMod 110262239) ^ 34 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_120259049 : Nat.Prime 120259049 := by
  apply lucas_primality 120259049 (6 : ZMod 120259049)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 2), (97, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 2), (97, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 120259049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_97
      · exact prime_ninetyFourCN_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 120259049) ^ 60129524 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 120259049) ^ 17179864 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 120259049) ^ 9250696 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 120259049) ^ 1239784 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 120259049) ^ 918008 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_140617229 : Nat.Prime 140617229 := by
  apply lucas_primality 140617229 (2 : ZMod 140617229)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251, 1), (140057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251, 1), (140057, 1)] : List FactorBlock).map factorBlockValue).prod) = 140617229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_251
      · exact prime_ninetyFourCN_140057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140617229) ^ 70308614 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 140617229) ^ 560228 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 140617229) ^ 1004 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_159363821 : Nat.Prime 159363821 := by
  apply lucas_primality 159363821 (2 : ZMod 159363821)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (103483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (103483, 1)] : List FactorBlock).map factorBlockValue).prod) = 159363821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_103483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159363821) ^ 79681910 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 159363821) ^ 31872764 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 159363821) ^ 22766260 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 159363821) ^ 14487620 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 159363821) ^ 1540 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_161131097 : Nat.Prime 161131097 := by
  apply lucas_primality 161131097 (3 : ZMod 161131097)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (199, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (199, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 161131097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_199
      · exact prime_ninetyFourCN_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 161131097) ^ 80565548 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 161131097) ^ 23018728 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 161131097) ^ 8480584 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 161131097) ^ 809704 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 161131097) ^ 211736 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_169536299 : Nat.Prime 169536299 := by
  apply lucas_primality 169536299 (2 : ZMod 169536299)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (1021303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (1021303, 1)] : List FactorBlock).map factorBlockValue).prod) = 169536299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_83
      · exact prime_ninetyFourCN_1021303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 169536299) ^ 84768149 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 169536299) ^ 2042606 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 169536299) ^ 166 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_170865581 : Nat.Prime 170865581 := by
  apply lucas_primality 170865581 (2 : ZMod 170865581)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8543279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8543279, 1)] : List FactorBlock).map factorBlockValue).prod) = 170865581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_8543279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 170865581) ^ 85432790 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 170865581) ^ 34173116 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 170865581) ^ 20 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_205419017 : Nat.Prime 205419017 := by
  apply lucas_primality 205419017 (5 : ZMod 205419017)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (2334307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (2334307, 1)] : List FactorBlock).map factorBlockValue).prod) = 205419017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_2334307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 205419017) ^ 102709508 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 205419017) ^ 18674456 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 205419017) ^ 88 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_206160359 : Nat.Prime 206160359 := by
  apply lucas_primality 206160359 (11 : ZMod 206160359)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (1163, 1), (1453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (1163, 1), (1453, 1)] : List FactorBlock).map factorBlockValue).prod) = 206160359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_61
      · exact prime_ninetyFourCN_1163
      · exact prime_ninetyFourCN_1453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 206160359) ^ 103080179 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 206160359) ^ 3379678 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 206160359) ^ 177266 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 206160359) ^ 141886 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_210011117 : Nat.Prime 210011117 := by
  apply lucas_primality 210011117 (2 : ZMod 210011117)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (7500397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (7500397, 1)] : List FactorBlock).map factorBlockValue).prod) = 210011117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_7500397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 210011117) ^ 105005558 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 210011117) ^ 30001588 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 210011117) ^ 28 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_215966279 : Nat.Prime 215966279 := by
  apply lucas_primality 215966279 (7 : ZMod 215966279)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (109, 1), (113, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (109, 1), (113, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 215966279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_109
      · exact prime_ninetyFourCN_113
      · exact prime_ninetyFourCN_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 215966279) ^ 107983139 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 215966279) ^ 19633298 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 215966279) ^ 1981342 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 215966279) ^ 1911206 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 215966279) ^ 270974 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_244383481 : Nat.Prime 244383481 := by
  apply lucas_primality 244383481 (14 : ZMod 244383481)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (11, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (11, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod) = 244383481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_6857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 244383481) ^ 122191740 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 244383481) ^ 81461160 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 244383481) ^ 48876696 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 244383481) ^ 22216680 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 244383481) ^ 35640 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_269708521 : Nat.Prime 269708521 := by
  apply lucas_primality 269708521 (14 : ZMod 269708521)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (53, 1), (42407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (53, 1), (42407, 1)] : List FactorBlock).map factorBlockValue).prod) = 269708521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_53
      · exact prime_ninetyFourCN_42407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 269708521) ^ 134854260 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 269708521) ^ 89902840 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 269708521) ^ 53941704 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 269708521) ^ 5088840 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 269708521) ^ 6360 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_279789901 : Nat.Prime 279789901 := by
  apply lucas_primality 279789901 (2 : ZMod 279789901)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (71741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (71741, 1)] : List FactorBlock).map factorBlockValue).prod) = 279789901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_71741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 279789901) ^ 139894950 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 279789901) ^ 93263300 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 279789901) ^ 55957980 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 279789901) ^ 21522300 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 279789901) ^ 3900 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_299808869 : Nat.Prime 299808869 := by
  apply lucas_primality 299808869 (2 : ZMod 299808869)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1801, 1), (41617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1801, 1), (41617, 1)] : List FactorBlock).map factorBlockValue).prod) = 299808869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_1801
      · exact prime_ninetyFourCN_41617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 299808869) ^ 149904434 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 299808869) ^ 166468 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 299808869) ^ 7204 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_335100679 : Nat.Prime 335100679 := by
  apply lucas_primality 335100679 (3 : ZMod 335100679)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5077283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5077283, 1)] : List FactorBlock).map factorBlockValue).prod) = 335100679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_5077283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 335100679) ^ 167550339 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 335100679) ^ 111700226 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 335100679) ^ 30463698 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 335100679) ^ 66 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_341596159 : Nat.Prime 341596159 := by
  apply lucas_primality 341596159 (3 : ZMod 341596159)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (761, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (761, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 341596159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_79
      · exact prime_ninetyFourCN_761
      · exact prime_ninetyFourCN_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 341596159) ^ 170798079 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 341596159) ^ 113865386 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 341596159) ^ 4324002 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 341596159) ^ 448878 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 341596159) ^ 360714 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_362769263 : Nat.Prime 362769263 := by
  apply lucas_primality 362769263 (5 : ZMod 362769263)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (2185357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (2185357, 1)] : List FactorBlock).map factorBlockValue).prod) = 362769263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_83
      · exact prime_ninetyFourCN_2185357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362769263) ^ 181384631 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 362769263) ^ 4370714 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 362769263) ^ 166 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_431527597 : Nat.Prime 431527597 := by
  apply lucas_primality 431527597 (5 : ZMod 431527597)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (683, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (683, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) = 431527597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_683
      · exact prime_ninetyFourCN_1423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 431527597) ^ 215763798 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 431527597) ^ 143842532 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 431527597) ^ 11662908 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 431527597) ^ 631812 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 431527597) ^ 303252 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_480645103 : Nat.Prime 480645103 := by
  apply lucas_primality 480645103 (3 : ZMod 480645103)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11443931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11443931, 1)] : List FactorBlock).map factorBlockValue).prod) = 480645103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_11443931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 480645103) ^ 240322551 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 480645103) ^ 160215034 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 480645103) ^ 68663586 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 480645103) ^ 42 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_494353009 : Nat.Prime 494353009 := by
  apply lucas_primality 494353009 (7 : ZMod 494353009)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (3433007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (3433007, 1)] : List FactorBlock).map factorBlockValue).prod) = 494353009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_3433007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 494353009) ^ 247176504 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 494353009) ^ 164784336 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 494353009) ^ 144 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_592197383 : Nat.Prime 592197383 := by
  apply lucas_primality 592197383 (5 : ZMod 592197383)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (42299813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (42299813, 1)] : List FactorBlock).map factorBlockValue).prod) = 592197383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_42299813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 592197383) ^ 296098691 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 592197383) ^ 84599626 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 592197383) ^ 14 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_638405987 : Nat.Prime 638405987 := by
  apply lucas_primality 638405987 (2 : ZMod 638405987)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (13878391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (13878391, 1)] : List FactorBlock).map factorBlockValue).prod) = 638405987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_13878391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 638405987) ^ 319202993 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 638405987) ^ 27756782 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 638405987) ^ 46 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_643459277 : Nat.Prime 643459277 := by
  apply lucas_primality 643459277 (2 : ZMod 643459277)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10501, 1), (15319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10501, 1), (15319, 1)] : List FactorBlock).map factorBlockValue).prod) = 643459277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_10501
      · exact prime_ninetyFourCN_15319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 643459277) ^ 321729638 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 643459277) ^ 61276 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 643459277) ^ 42004 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_708016301 : Nat.Prime 708016301 := by
  apply lucas_primality 708016301 (7 : ZMod 708016301)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (349, 1), (20287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (349, 1), (20287, 1)] : List FactorBlock).map factorBlockValue).prod) = 708016301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_349
      · exact prime_ninetyFourCN_20287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 708016301) ^ 354008150 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 708016301) ^ 141603260 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 708016301) ^ 2028700 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 708016301) ^ 34900 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_774173273 : Nat.Prime 774173273 := by
  apply lucas_primality 774173273 (3 : ZMod 774173273)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5717, 1), (16927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5717, 1), (16927, 1)] : List FactorBlock).map factorBlockValue).prod) = 774173273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5717
      · exact prime_ninetyFourCN_16927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 774173273) ^ 387086636 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 774173273) ^ 135416 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 774173273) ^ 45736 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_802096013 : Nat.Prime 802096013 := by
  apply lucas_primality 802096013 (2 : ZMod 802096013)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1123, 1), (178561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1123, 1), (178561, 1)] : List FactorBlock).map factorBlockValue).prod) = 802096013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_1123
      · exact prime_ninetyFourCN_178561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 802096013) ^ 401048006 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 802096013) ^ 714244 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 802096013) ^ 4492 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_850414727 : Nat.Prime 850414727 := by
  apply lucas_primality 850414727 (5 : ZMod 850414727)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (60743909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (60743909, 1)] : List FactorBlock).map factorBlockValue).prod) = 850414727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_60743909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 850414727) ^ 425207363 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 850414727) ^ 121487818 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 850414727) ^ 14 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_911142601 : Nat.Prime 911142601 := by
  apply lucas_primality 911142601 (13 : ZMod 911142601)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (1518571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (1518571, 1)] : List FactorBlock).map factorBlockValue).prod) = 911142601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_1518571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 911142601) ^ 455571300 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 911142601) ^ 303714200 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 911142601) ^ 182228520 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 911142601) ^ 600 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1080506591 : Nat.Prime 1080506591 := by
  apply lucas_primality 1080506591 (13 : ZMod 1080506591)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (108050659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (108050659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080506591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_108050659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1080506591) ^ 540253295 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1080506591) ^ 216101318 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1080506591) ^ 10 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1177193573 : Nat.Prime 1177193573 := by
  apply lucas_primality 1177193573 (2 : ZMod 1177193573)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (337, 1), (5861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (337, 1), (5861, 1)] : List FactorBlock).map factorBlockValue).prod) = 1177193573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_149
      · exact prime_ninetyFourCN_337
      · exact prime_ninetyFourCN_5861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1177193573) ^ 588596786 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177193573) ^ 7900628 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177193573) ^ 3493156 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1177193573) ^ 200852 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1184394767 : Nat.Prime 1184394767 := by
  apply lucas_primality 1184394767 (5 : ZMod 1184394767)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (592197383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (592197383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1184394767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_592197383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1184394767) ^ 592197383 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1184394767) ^ 2 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1350669071 : Nat.Prime 1350669071 := by
  apply lucas_primality 1350669071 (13 : ZMod 1350669071)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (4356997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (4356997, 1)] : List FactorBlock).map factorBlockValue).prod) = 1350669071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_31
      · exact prime_ninetyFourCN_4356997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1350669071) ^ 675334535 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1350669071) ^ 270133814 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1350669071) ^ 43569970 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1350669071) ^ 310 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1587172177 : Nat.Prime 1587172177 := by
  apply lucas_primality 1587172177 (5 : ZMod 1587172177)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (101, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (101, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1587172177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_61
      · exact prime_ninetyFourCN_101
      · exact prime_ninetyFourCN_1789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1587172177) ^ 793586088 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1587172177) ^ 529057392 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1587172177) ^ 26019216 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1587172177) ^ 15714576 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1587172177) ^ 887184 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1754978047 : Nat.Prime 1754978047 := by
  apply lucas_primality 1754978047 (5 : ZMod 1754978047)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (509, 1), (2917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (509, 1), (2917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1754978047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_197
      · exact prime_ninetyFourCN_509
      · exact prime_ninetyFourCN_2917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1754978047) ^ 877489023 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1754978047) ^ 584992682 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1754978047) ^ 8908518 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1754978047) ^ 3447894 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1754978047) ^ 601638 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1909110953 : Nat.Prime 1909110953 := by
  apply lucas_primality 1909110953 (3 : ZMod 1909110953)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (23, 1), (211747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (23, 1), (211747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1909110953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_211747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1909110953) ^ 954555476 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1909110953) ^ 272730136 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1909110953) ^ 83004824 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1909110953) ^ 9016 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2163015313 : Nat.Prime 2163015313 := by
  apply lucas_primality 2163015313 (10 : ZMod 2163015313)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (1959253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (1959253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2163015313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_1959253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2163015313) ^ 1081507656 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2163015313) ^ 721005104 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2163015313) ^ 94044144 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2163015313) ^ 1104 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2294403259 : Nat.Prime 2294403259 := by
  apply lucas_primality 2294403259 (3 : ZMod 2294403259)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (54628649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (54628649, 1)] : List FactorBlock).map factorBlockValue).prod) = 2294403259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_54628649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2294403259) ^ 1147201629 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2294403259) ^ 764801086 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2294403259) ^ 327771894 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2294403259) ^ 42 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2348364509 : Nat.Prime 2348364509 := by
  apply lucas_primality 2348364509 (2 : ZMod 2348364509)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (4414219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (4414219, 1)] : List FactorBlock).map factorBlockValue).prod) = 2348364509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_4414219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2348364509) ^ 1174182254 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2348364509) ^ 335480644 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2348364509) ^ 123598132 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2348364509) ^ 532 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2413580947 : Nat.Prime 2413580947 := by
  apply lucas_primality 2413580947 (2 : ZMod 2413580947)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (23, 1), (356933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (23, 1), (356933, 1)] : List FactorBlock).map factorBlockValue).prod) = 2413580947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_356933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2413580947) ^ 1206790473 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413580947) ^ 804526982 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413580947) ^ 344797278 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413580947) ^ 104938302 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413580947) ^ 6762 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2422358971 : Nat.Prime 2422358971 := by
  apply lucas_primality 2422358971 (7 : ZMod 2422358971)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1847, 1), (43717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1847, 1), (43717, 1)] : List FactorBlock).map factorBlockValue).prod) = 2422358971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_1847
      · exact prime_ninetyFourCN_43717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2422358971) ^ 1211179485 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2422358971) ^ 807452990 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2422358971) ^ 484471794 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2422358971) ^ 1311510 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2422358971) ^ 55410 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2699696561 : Nat.Prime 2699696561 := by
  apply lucas_primality 2699696561 (3 : ZMod 2699696561)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (17, 1), (113, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (17, 1), (113, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 2699696561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_113
      · exact prime_ninetyFourCN_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2699696561) ^ 1349848280 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2699696561) ^ 539939312 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2699696561) ^ 245426960 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2699696561) ^ 158805680 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2699696561) ^ 23891120 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2699696561) ^ 1690480 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2708996369 : Nat.Prime 2708996369 := by
  apply lucas_primality 2708996369 (3 : ZMod 2708996369)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (13024021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (13024021, 1)] : List FactorBlock).map factorBlockValue).prod) = 2708996369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_13024021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2708996369) ^ 1354498184 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2708996369) ^ 208384336 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2708996369) ^ 208 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2797899011 : Nat.Prime 2797899011 := by
  apply lucas_primality 2797899011 (10 : ZMod 2797899011)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (279789901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (279789901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2797899011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_279789901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 2797899011) ^ 1398949505 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2797899011) ^ 559579802 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2797899011) ^ 10 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3533299051 : Nat.Prime 3533299051 := by
  apply lucas_primality 3533299051 (2 : ZMod 3533299051)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1721, 1), (13687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1721, 1), (13687, 1)] : List FactorBlock).map factorBlockValue).prod) = 3533299051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_1721
      · exact prime_ninetyFourCN_13687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3533299051) ^ 1766649525 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3533299051) ^ 1177766350 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3533299051) ^ 706659810 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3533299051) ^ 2053050 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3533299051) ^ 258150 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3682938953 : Nat.Prime 3682938953 := by
  apply lucas_primality 3682938953 (5 : ZMod 3682938953)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 2), (367, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 2), (367, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) = 3682938953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_367
      · exact prime_ninetyFourCN_1481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3682938953) ^ 1841469476 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3682938953) ^ 526134136 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3682938953) ^ 334812632 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3682938953) ^ 10035256 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3682938953) ^ 2486792 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3847385747 : Nat.Prime 3847385747 := by
  apply lucas_primality 3847385747 (2 : ZMod 3847385747)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (167, 1), (397211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (167, 1), (397211, 1)] : List FactorBlock).map factorBlockValue).prod) = 3847385747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_29
      · exact prime_ninetyFourCN_167
      · exact prime_ninetyFourCN_397211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3847385747) ^ 1923692873 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3847385747) ^ 132668474 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3847385747) ^ 23038238 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3847385747) ^ 9686 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3962061647 : Nat.Prime 3962061647 := by
  apply lucas_primality 3962061647 (5 : ZMod 3962061647)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (14460079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (14460079, 1)] : List FactorBlock).map factorBlockValue).prod) = 3962061647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_137
      · exact prime_ninetyFourCN_14460079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3962061647) ^ 1981030823 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3962061647) ^ 28920158 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3962061647) ^ 274 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3977295653 : Nat.Prime 3977295653 := by
  apply lucas_primality 3977295653 (2 : ZMod 3977295653)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (311, 1), (26423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (311, 1), (26423, 1)] : List FactorBlock).map factorBlockValue).prod) = 3977295653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_311
      · exact prime_ninetyFourCN_26423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3977295653) ^ 1988647826 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3977295653) ^ 361572332 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3977295653) ^ 12788732 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3977295653) ^ 150524 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_4003908829 : Nat.Prime 4003908829 := by
  apply lucas_primality 4003908829 (2 : ZMod 4003908829)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (251, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (251, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) = 4003908829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_157
      · exact prime_ninetyFourCN_251
      · exact prime_ninetyFourCN_8467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4003908829) ^ 2001954414 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4003908829) ^ 1334636276 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4003908829) ^ 25502604 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4003908829) ^ 15951828 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4003908829) ^ 472884 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_4474018459 : Nat.Prime 4474018459 := by
  apply lucas_primality 4474018459 (3 : ZMod 4474018459)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 2), (163, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 2), (163, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) = 4474018459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_163
      · exact prime_ninetyFourCN_1289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4474018459) ^ 2237009229 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4474018459) ^ 1491339486 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4474018459) ^ 639145494 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4474018459) ^ 344155266 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4474018459) ^ 27447966 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4474018459) ^ 3470922 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_4947848617 : Nat.Prime 4947848617 := by
  apply lucas_primality 4947848617 (5 : ZMod 4947848617)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (206160359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (206160359, 1)] : List FactorBlock).map factorBlockValue).prod) = 4947848617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_206160359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4947848617) ^ 2473924308 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 4947848617) ^ 1649282872 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 4947848617) ^ 24 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5127438301 : Nat.Prime 5127438301 := by
  apply lucas_primality 5127438301 (2 : ZMod 5127438301)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (23, 2), (32309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (23, 2), (32309, 1)] : List FactorBlock).map factorBlockValue).prod) = 5127438301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_32309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5127438301) ^ 2563719150 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127438301) ^ 1709146100 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127438301) ^ 1025487660 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127438301) ^ 222932100 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5127438301) ^ 158700 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5335143521 : Nat.Prime 5335143521 := by
  apply lucas_primality 5335143521 (3 : ZMod 5335143521)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 2), (680503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 2), (680503, 1)] : List FactorBlock).map factorBlockValue).prod) = 5335143521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_680503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5335143521) ^ 2667571760 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5335143521) ^ 1067028704 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5335143521) ^ 762163360 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5335143521) ^ 7840 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5595798023 : Nat.Prime 5595798023 := by
  apply lucas_primality 5595798023 (5 : ZMod 5595798023)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2797899011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2797899011, 1)] : List FactorBlock).map factorBlockValue).prod) = 5595798023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_2797899011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 5595798023) ^ 2797899011 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5595798023) ^ 2 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5800719493 : Nat.Prime 5800719493 := by
  apply lucas_primality 5800719493 (5 : ZMod 5800719493)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (161131097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (161131097, 1)] : List FactorBlock).map factorBlockValue).prod) = 5800719493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_161131097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5800719493) ^ 2900359746 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5800719493) ^ 1933573164 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5800719493) ^ 36 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5865674987 : Nat.Prime 5865674987 := by
  apply lucas_primality 5865674987 (2 : ZMod 5865674987)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (751, 1), (21817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (751, 1), (21817, 1)] : List FactorBlock).map factorBlockValue).prod) = 5865674987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_179
      · exact prime_ninetyFourCN_751
      · exact prime_ninetyFourCN_21817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5865674987) ^ 2932837493 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5865674987) ^ 32769134 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5865674987) ^ 7810486 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5865674987) ^ 268858 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_6016807171 : Nat.Prime 6016807171 := by
  apply lucas_primality 6016807171 (2 : ZMod 6016807171)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (11, 1), (37, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (11, 1), (37, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) = 6016807171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_18251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6016807171) ^ 3008403585 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6016807171) ^ 2005602390 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6016807171) ^ 1203361434 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6016807171) ^ 546982470 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6016807171) ^ 162616410 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6016807171) ^ 329670 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_6775446043 : Nat.Prime 6775446043 := by
  apply lucas_primality 6775446043 (3 : ZMod 6775446043)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (13941247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (13941247, 1)] : List FactorBlock).map factorBlockValue).prod) = 6775446043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13941247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6775446043) ^ 3387723021 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6775446043) ^ 2258482014 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6775446043) ^ 486 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_8435294201 : Nat.Prime 8435294201 := by
  apply lucas_primality 8435294201 (3 : ZMod 8435294201)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (293, 1), (143947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (293, 1), (143947, 1)] : List FactorBlock).map factorBlockValue).prod) = 8435294201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_293
      · exact prime_ninetyFourCN_143947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8435294201) ^ 4217647100 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8435294201) ^ 1687058840 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8435294201) ^ 28789400 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 8435294201) ^ 58600 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_11229344183 : Nat.Prime 11229344183 := by
  apply lucas_primality 11229344183 (5 : ZMod 11229344183)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (802096013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (802096013, 1)] : List FactorBlock).map factorBlockValue).prod) = 11229344183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_802096013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11229344183) ^ 5614672091 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11229344183) ^ 1604192026 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 11229344183) ^ 14 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_11905806179 : Nat.Prime 11905806179 := by
  apply lucas_primality 11905806179 (2 : ZMod 11905806179)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (850414727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (850414727, 1)] : List FactorBlock).map factorBlockValue).prod) = 11905806179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_850414727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11905806179) ^ 5952903089 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11905806179) ^ 1700829454 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11905806179) ^ 14 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_18393863627 : Nat.Prime 18393863627 := by
  apply lucas_primality 18393863627 (2 : ZMod 18393863627)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (67, 1), (8074567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (67, 1), (8074567, 1)] : List FactorBlock).map factorBlockValue).prod) = 18393863627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_67
      · exact prime_ninetyFourCN_8074567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18393863627) ^ 9196931813 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 18393863627) ^ 1081991978 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 18393863627) ^ 274535278 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 18393863627) ^ 2278 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_20344355881 : Nat.Prime 20344355881 := by
  apply lucas_primality 20344355881 (13 : ZMod 20344355881)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (169536299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (169536299, 1)] : List FactorBlock).map factorBlockValue).prod) = 20344355881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_169536299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 20344355881) ^ 10172177940 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 20344355881) ^ 6781451960 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 20344355881) ^ 4068871176 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 20344355881) ^ 120 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_24312043279 : Nat.Prime 24312043279 := by
  apply lucas_primality 24312043279 (6 : ZMod 24312043279)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1350669071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1350669071, 1)] : List FactorBlock).map factorBlockValue).prod) = 24312043279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_1350669071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 24312043279) ^ 12156021639 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 24312043279) ^ 8104014426 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 24312043279) ^ 18 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_24756515093 : Nat.Prime 24756515093 := by
  apply lucas_primality 24756515093 (2 : ZMod 24756515093)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (1451, 1), (28627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (1451, 1), (28627, 1)] : List FactorBlock).map factorBlockValue).prod) = 24756515093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_149
      · exact prime_ninetyFourCN_1451
      · exact prime_ninetyFourCN_28627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24756515093) ^ 12378257546 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 24756515093) ^ 166151108 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 24756515093) ^ 17061692 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 24756515093) ^ 864796 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_26727553343 : Nat.Prime 26727553343 := by
  apply lucas_primality 26727553343 (5 : ZMod 26727553343)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1909110953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1909110953, 1)] : List FactorBlock).map factorBlockValue).prod) = 26727553343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_1909110953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26727553343) ^ 13363776671 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 26727553343) ^ 3818221906 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 26727553343) ^ 14 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_28665443069 : Nat.Prime 28665443069 := by
  apply lucas_primality 28665443069 (2 : ZMod 28665443069)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (47, 1), (101, 1), (36821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (47, 1), (101, 1), (36821, 1)] : List FactorBlock).map factorBlockValue).prod) = 28665443069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_41
      · exact prime_ninetyFourCN_47
      · exact prime_ninetyFourCN_101
      · exact prime_ninetyFourCN_36821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28665443069) ^ 14332721534 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 28665443069) ^ 699157148 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 28665443069) ^ 609903044 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 28665443069) ^ 283816268 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 28665443069) ^ 778508 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_29992825349 : Nat.Prime 29992825349 := by
  apply lucas_primality 29992825349 (2 : ZMod 29992825349)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (59, 1), (269, 1), (27791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (59, 1), (269, 1), (27791, 1)] : List FactorBlock).map factorBlockValue).prod) = 29992825349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_59
      · exact prime_ninetyFourCN_269
      · exact prime_ninetyFourCN_27791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29992825349) ^ 14996412674 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 29992825349) ^ 1764283844 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 29992825349) ^ 508352972 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 29992825349) ^ 111497492 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 29992825349) ^ 1079228 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_30254532601 : Nat.Prime 30254532601 := by
  apply lucas_primality 30254532601 (7 : ZMod 30254532601)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (50424221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (50424221, 1)] : List FactorBlock).map factorBlockValue).prod) = 30254532601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_50424221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 30254532601) ^ 15127266300 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 30254532601) ^ 10084844200 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 30254532601) ^ 6050906520 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 30254532601) ^ 600 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_32258619493 : Nat.Prime 32258619493 := by
  apply lucas_primality 32258619493 (5 : ZMod 32258619493)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (244383481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (244383481, 1)] : List FactorBlock).map factorBlockValue).prod) = 32258619493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_244383481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32258619493) ^ 16129309746 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 32258619493) ^ 10752873164 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 32258619493) ^ 2932601772 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 32258619493) ^ 132 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_32907634183 : Nat.Prime 32907634183 := by
  apply lucas_primality 32907634183 (3 : ZMod 32907634183)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (103, 1), (5916511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (103, 1), (5916511, 1)] : List FactorBlock).map factorBlockValue).prod) = 32907634183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_103
      · exact prime_ninetyFourCN_5916511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32907634183) ^ 16453817091 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32907634183) ^ 10969211394 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32907634183) ^ 319491594 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32907634183) ^ 5562 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_41339518439 : Nat.Prime 41339518439 := by
  apply lucas_primality 41339518439 (7 : ZMod 41339518439)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (587, 1), (5653, 1), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (587, 1), (5653, 1), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) = 41339518439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_587
      · exact prime_ninetyFourCN_5653
      · exact prime_ninetyFourCN_6229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 41339518439) ^ 20669759219 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41339518439) ^ 70425074 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41339518439) ^ 7312846 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41339518439) ^ 6636622 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_45694267477 : Nat.Prime 45694267477 := by
  apply lucas_primality 45694267477 (2 : ZMod 45694267477)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (3797, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (3797, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) = 45694267477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_3797
      · exact prime_ninetyFourCN_7013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45694267477) ^ 22847133738 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 45694267477) ^ 15231422492 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 45694267477) ^ 4154024316 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 45694267477) ^ 3514943652 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 45694267477) ^ 12034308 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 45694267477) ^ 6515652 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_60269161829 : Nat.Prime 60269161829 := by
  apply lucas_primality 60269161829 (2 : ZMod 60269161829)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (457, 1), (911, 1), (36191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (457, 1), (911, 1), (36191, 1)] : List FactorBlock).map factorBlockValue).prod) = 60269161829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_457
      · exact prime_ninetyFourCN_911
      · exact prime_ninetyFourCN_36191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60269161829) ^ 30134580914 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60269161829) ^ 131880004 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60269161829) ^ 66157148 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 60269161829) ^ 1665308 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_62670161779 : Nat.Prime 62670161779 := by
  apply lucas_primality 62670161779 (2 : ZMod 62670161779)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (14533, 1), (102673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (14533, 1), (102673, 1)] : List FactorBlock).map factorBlockValue).prod) = 62670161779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_14533
      · exact prime_ninetyFourCN_102673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62670161779) ^ 31335080889 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62670161779) ^ 20890053926 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62670161779) ^ 8952880254 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62670161779) ^ 4312266 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62670161779) ^ 610386 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_63454067321 : Nat.Prime 63454067321 := by
  apply lucas_primality 63454067321 (3 : ZMod 63454067321)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (1303, 1), (173923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (1303, 1), (173923, 1)] : List FactorBlock).map factorBlockValue).prod) = 63454067321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_1303
      · exact prime_ninetyFourCN_173923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63454067321) ^ 31727033660 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 63454067321) ^ 12690813464 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 63454067321) ^ 9064866760 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 63454067321) ^ 48698440 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 63454067321) ^ 364840 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_65645447467 : Nat.Prime 65645447467 := by
  apply lucas_primality 65645447467 (14 : ZMod 65645447467)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (131, 1), (1246543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (131, 1), (1246543, 1)] : List FactorBlock).map factorBlockValue).prod) = 65645447467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_67
      · exact prime_ninetyFourCN_131
      · exact prime_ninetyFourCN_1246543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 65645447467) ^ 32822723733 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 65645447467) ^ 21881815822 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 65645447467) ^ 979782798 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 65645447467) ^ 501110286 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 65645447467) ^ 52662 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_67011265939 : Nat.Prime 67011265939 := by
  apply lucas_primality 67011265939 (3 : ZMod 67011265939)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (443, 1), (25211161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (443, 1), (25211161, 1)] : List FactorBlock).map factorBlockValue).prod) = 67011265939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_443
      · exact prime_ninetyFourCN_25211161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 67011265939) ^ 33505632969 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67011265939) ^ 22337088646 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67011265939) ^ 151266966 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 67011265939) ^ 2658 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_70100964083 : Nat.Prime 70100964083 := by
  apply lucas_primality 70100964083 (2 : ZMod 70100964083)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (67, 1), (113, 1), (149341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (67, 1), (113, 1), (149341, 1)] : List FactorBlock).map factorBlockValue).prod) = 70100964083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_31
      · exact prime_ninetyFourCN_67
      · exact prime_ninetyFourCN_113
      · exact prime_ninetyFourCN_149341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70100964083) ^ 35050482041 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70100964083) ^ 2261321422 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70100964083) ^ 1046283046 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70100964083) ^ 620362514 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70100964083) ^ 469402 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_72407428411 : Nat.Prime 72407428411 := by
  apply lucas_primality 72407428411 (2 : ZMod 72407428411)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2413580947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2413580947, 1)] : List FactorBlock).map factorBlockValue).prod) = 72407428411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_2413580947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72407428411) ^ 36203714205 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 72407428411) ^ 24135809470 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 72407428411) ^ 14481485682 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 72407428411) ^ 30 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_75033708329 : Nat.Prime 75033708329 := by
  apply lucas_primality 75033708329 (3 : ZMod 75033708329)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2239, 1), (4189019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2239, 1), (4189019, 1)] : List FactorBlock).map factorBlockValue).prod) = 75033708329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_2239
      · exact prime_ninetyFourCN_4189019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 75033708329) ^ 37516854164 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 75033708329) ^ 33512152 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 75033708329) ^ 17912 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_97243030349 : Nat.Prime 97243030349 := by
  apply lucas_primality 97243030349 (2 : ZMod 97243030349)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (1433, 1), (413779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (1433, 1), (413779, 1)] : List FactorBlock).map factorBlockValue).prod) = 97243030349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_41
      · exact prime_ninetyFourCN_1433
      · exact prime_ninetyFourCN_413779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97243030349) ^ 48621515174 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 97243030349) ^ 2371781228 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 97243030349) ^ 67859756 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 97243030349) ^ 235012 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_126908134643 : Nat.Prime 126908134643 := by
  apply lucas_primality 126908134643 (2 : ZMod 126908134643)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (63454067321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (63454067321, 1)] : List FactorBlock).map factorBlockValue).prod) = 126908134643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_63454067321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 126908134643) ^ 63454067321 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 126908134643) ^ 2 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_128175598951 : Nat.Prime 128175598951 := by
  apply lucas_primality 128175598951 (3 : ZMod 128175598951)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 2), (17438857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 2), (17438857, 1)] : List FactorBlock).map factorBlockValue).prod) = 128175598951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_17438857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128175598951) ^ 64087799475 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 128175598951) ^ 42725199650 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 128175598951) ^ 25635119790 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 128175598951) ^ 18310799850 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 128175598951) ^ 7350 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_130893311789 : Nat.Prime 130893311789 := by
  apply lucas_primality 130893311789 (2 : ZMod 130893311789)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 2), (61858843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 2), (61858843, 1)] : List FactorBlock).map factorBlockValue).prod) = 130893311789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_61858843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 130893311789) ^ 65446655894 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 130893311789) ^ 5691013556 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 130893311789) ^ 2116 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_137962282519 : Nat.Prime 137962282519 := by
  apply lucas_primality 137962282519 (3 : ZMod 137962282519)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6569, 1), (1166779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6569, 1), (1166779, 1)] : List FactorBlock).map factorBlockValue).prod) = 137962282519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_6569
      · exact prime_ninetyFourCN_1166779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137962282519) ^ 68981141259 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 137962282519) ^ 45987427506 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 137962282519) ^ 21002022 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 137962282519) ^ 118242 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_167176426163 : Nat.Prime 167176426163 := by
  apply lucas_primality 167176426163 (2 : ZMod 167176426163)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (81509, 1), (1025509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (81509, 1), (1025509, 1)] : List FactorBlock).map factorBlockValue).prod) = 167176426163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_81509
      · exact prime_ninetyFourCN_1025509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 167176426163) ^ 83588213081 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167176426163) ^ 2051018 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167176426163) ^ 163018 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_197445805099 : Nat.Prime 197445805099 := by
  apply lucas_primality 197445805099 (2 : ZMod 197445805099)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32907634183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32907634183, 1)] : List FactorBlock).map factorBlockValue).prod) = 197445805099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_32907634183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 197445805099) ^ 98722902549 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 197445805099) ^ 65815268366 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 197445805099) ^ 6 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_208183563127 : Nat.Prime 208183563127 := by
  apply lucas_primality 208183563127 (3 : ZMod 208183563127)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (11, 1), (103, 1), (54011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (11, 1), (103, 1), (54011, 1)] : List FactorBlock).map factorBlockValue).prod) = 208183563127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_103
      · exact prime_ninetyFourCN_54011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 208183563127) ^ 104091781563 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 208183563127) ^ 69394521042 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 208183563127) ^ 29740509018 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 208183563127) ^ 18925778466 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 208183563127) ^ 2021199642 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 208183563127) ^ 3854466 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_233960920549 : Nat.Prime 233960920549 := by
  apply lucas_primality 233960920549 (2 : ZMod 233960920549)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2357, 1), (8271847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2357, 1), (8271847, 1)] : List FactorBlock).map factorBlockValue).prod) = 233960920549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_2357
      · exact prime_ninetyFourCN_8271847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 233960920549) ^ 116980460274 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 233960920549) ^ 77986973516 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 233960920549) ^ 99262164 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 233960920549) ^ 28284 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_253168883431 : Nat.Prime 253168883431 := by
  apply lucas_primality 253168883431 (3 : ZMod 253168883431)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (45677, 1), (184753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (45677, 1), (184753, 1)] : List FactorBlock).map factorBlockValue).prod) = 253168883431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_45677
      · exact prime_ninetyFourCN_184753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 253168883431) ^ 126584441715 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 253168883431) ^ 84389627810 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 253168883431) ^ 50633776686 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 253168883431) ^ 5542590 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 253168883431) ^ 1370310 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_313133490419 : Nat.Prime 313133490419 := by
  apply lucas_primality 313133490419 (2 : ZMod 313133490419)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (1177193573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (1177193573, 1)] : List FactorBlock).map factorBlockValue).prod) = 313133490419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_1177193573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 313133490419) ^ 156566745209 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 313133490419) ^ 44733355774 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 313133490419) ^ 16480710022 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 313133490419) ^ 266 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_336328341637 : Nat.Prime 336328341637 := by
  apply lucas_primality 336328341637 (5 : ZMod 336328341637)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (4003908829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (4003908829, 1)] : List FactorBlock).map factorBlockValue).prod) = 336328341637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_4003908829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 336328341637) ^ 168164170818 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 336328341637) ^ 112109447212 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 336328341637) ^ 48046905948 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 336328341637) ^ 84 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_363559990597 : Nat.Prime 363559990597 := by
  apply lucas_primality 363559990597 (5 : ZMod 363559990597)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1171, 1), (2352043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1171, 1), (2352043, 1)] : List FactorBlock).map factorBlockValue).prod) = 363559990597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_1171
      · exact prime_ninetyFourCN_2352043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 363559990597) ^ 181779995298 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 363559990597) ^ 121186663532 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 363559990597) ^ 33050908236 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 363559990597) ^ 310469676 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 363559990597) ^ 154572 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_397188561557 : Nat.Prime 397188561557 := by
  apply lucas_primality 397188561557 (2 : ZMod 397188561557)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (43, 1), (149, 1), (418871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (43, 1), (149, 1), (418871, 1)] : List FactorBlock).map factorBlockValue).prod) = 397188561557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_43
      · exact prime_ninetyFourCN_149
      · exact prime_ninetyFourCN_418871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 397188561557) ^ 198594280778 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397188561557) ^ 10734825988 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397188561557) ^ 9236943292 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397188561557) ^ 2665695044 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397188561557) ^ 948236 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_422125661561 : Nat.Prime 422125661561 := by
  apply lucas_primality 422125661561 (3 : ZMod 422125661561)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73673, 1), (143243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73673, 1), (143243, 1)] : List FactorBlock).map factorBlockValue).prod) = 422125661561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_73673
      · exact prime_ninetyFourCN_143243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 422125661561) ^ 211062830780 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 422125661561) ^ 84425132312 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 422125661561) ^ 5729720 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 422125661561) ^ 2946920 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_557404756561 : Nat.Prime 557404756561 := by
  apply lucas_primality 557404756561 (17 : ZMod 557404756561)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (774173273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (774173273, 1)] : List FactorBlock).map factorBlockValue).prod) = 557404756561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_774173273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 557404756561) ^ 278702378280 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 557404756561) ^ 185801585520 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 557404756561) ^ 111480951312 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 557404756561) ^ 720 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_594976997327 : Nat.Prime 594976997327 := by
  apply lucas_primality 594976997327 (5 : ZMod 594976997327)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1103, 1), (269708521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1103, 1), (269708521, 1)] : List FactorBlock).map factorBlockValue).prod) = 594976997327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_1103
      · exact prime_ninetyFourCN_269708521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 594976997327) ^ 297488498663 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 594976997327) ^ 539417042 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 594976997327) ^ 2206 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_657952947679 : Nat.Prime 657952947679 := by
  apply lucas_primality 657952947679 (3 : ZMod 657952947679)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (8435294201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (8435294201, 1)] : List FactorBlock).map factorBlockValue).prod) = 657952947679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_8435294201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 657952947679) ^ 328976473839 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 657952947679) ^ 219317649226 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 657952947679) ^ 50611765206 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 657952947679) ^ 78 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_724074284111 : Nat.Prime 724074284111 := by
  apply lucas_primality 724074284111 (17 : ZMod 724074284111)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (72407428411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (72407428411, 1)] : List FactorBlock).map factorBlockValue).prod) = 724074284111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_72407428411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 724074284111) ^ 362037142055 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 724074284111) ^ 144814856822 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 724074284111) ^ 10 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_726085982341 : Nat.Prime 726085982341 := by
  apply lucas_primality 726085982341 (2 : ZMod 726085982341)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (6337, 1), (212183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (6337, 1), (212183, 1)] : List FactorBlock).map factorBlockValue).prod) = 726085982341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_6337
      · exact prime_ninetyFourCN_212183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 726085982341) ^ 363042991170 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 726085982341) ^ 242028660780 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 726085982341) ^ 145217196468 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 726085982341) ^ 114578820 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 726085982341) ^ 3421980 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_775907325041 : Nat.Prime 775907325041 := by
  apply lucas_primality 775907325041 (6 : ZMod 775907325041)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (829, 1), (11699447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (829, 1), (11699447, 1)] : List FactorBlock).map factorBlockValue).prod) = 775907325041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_829
      · exact prime_ninetyFourCN_11699447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 775907325041) ^ 387953662520 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 775907325041) ^ 155181465008 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 775907325041) ^ 935955760 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 775907325041) ^ 66320 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_852782688127 : Nat.Prime 852782688127 := by
  apply lucas_primality 852782688127 (3 : ZMod 852782688127)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (36607, 1), (1294201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (36607, 1), (1294201, 1)] : List FactorBlock).map factorBlockValue).prod) = 852782688127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_36607
      · exact prime_ninetyFourCN_1294201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 852782688127) ^ 426391344063 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 852782688127) ^ 284260896042 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 852782688127) ^ 23295618 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 852782688127) ^ 658926 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_878773418023 : Nat.Prime 878773418023 := by
  apply lucas_primality 878773418023 (3 : ZMod 878773418023)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (233, 1), (5023, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (233, 1), (5023, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) = 878773418023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_233
      · exact prime_ninetyFourCN_5023
      · exact prime_ninetyFourCN_5441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 878773418023) ^ 439386709011 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 878773418023) ^ 292924472674 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 878773418023) ^ 38207539914 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 878773418023) ^ 3771559734 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 878773418023) ^ 174949914 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 878773418023) ^ 161509542 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_935843682197 : Nat.Prime 935843682197 := by
  apply lucas_primality 935843682197 (2 : ZMod 935843682197)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233960920549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233960920549, 1)] : List FactorBlock).map factorBlockValue).prod) = 935843682197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_233960920549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 935843682197) ^ 467921841098 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 935843682197) ^ 4 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1071503698777 : Nat.Prime 1071503698777 := by
  apply lucas_primality 1071503698777 (5 : ZMod 1071503698777)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (911142601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (911142601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1071503698777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_911142601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1071503698777) ^ 535751849388 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071503698777) ^ 357167899592 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071503698777) ^ 153071956968 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071503698777) ^ 1176 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1170041284417 : Nat.Prime 1170041284417 := by
  apply lucas_primality 1170041284417 (7 : ZMod 1170041284417)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (23, 1), (2081, 1), (127321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (23, 1), (2081, 1), (127321, 1)] : List FactorBlock).map factorBlockValue).prod) = 1170041284417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_2081
      · exact prime_ninetyFourCN_127321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1170041284417) ^ 585020642208 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1170041284417) ^ 390013761472 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1170041284417) ^ 50871360192 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1170041284417) ^ 562249536 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1170041284417) ^ 9189696 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1299515586973 : Nat.Prime 1299515586973 := by
  apply lucas_primality 1299515586973 (6 : ZMod 1299515586973)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1619, 1), (66888799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1619, 1), (66888799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299515586973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_1619
      · exact prime_ninetyFourCN_66888799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1299515586973) ^ 649757793486 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1299515586973) ^ 433171862324 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1299515586973) ^ 802665588 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1299515586973) ^ 19428 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1379734969453 : Nat.Prime 1379734969453 := by
  apply lucas_primality 1379734969453 (2 : ZMod 1379734969453)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (479, 1), (2017121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (479, 1), (2017121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1379734969453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_479
      · exact prime_ninetyFourCN_2017121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1379734969453) ^ 689867484726 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379734969453) ^ 459911656484 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379734969453) ^ 197104995636 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379734969453) ^ 81160880556 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379734969453) ^ 2880448788 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379734969453) ^ 684012 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1439655616753 : Nat.Prime 1439655616753 := by
  apply lucas_primality 1439655616753 (5 : ZMod 1439655616753)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29992825349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29992825349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439655616753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_29992825349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1439655616753) ^ 719827808376 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1439655616753) ^ 479885205584 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1439655616753) ^ 48 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1496742987209 : Nat.Prime 1496742987209 := by
  apply lucas_primality 1496742987209 (3 : ZMod 1496742987209)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (26727553343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (26727553343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1496742987209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_26727553343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1496742987209) ^ 748371493604 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1496742987209) ^ 213820426744 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1496742987209) ^ 56 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1780228230871 : Nat.Prime 1780228230871 := by
  apply lucas_primality 1780228230871 (3 : ZMod 1780228230871)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (67, 1), (23937451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (67, 1), (23937451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1780228230871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_67
      · exact prime_ninetyFourCN_23937451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1780228230871) ^ 890114115435 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1780228230871) ^ 593409410290 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1780228230871) ^ 356045646174 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1780228230871) ^ 48114276510 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1780228230871) ^ 26570570610 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1780228230871) ^ 74370 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2301400095931 : Nat.Prime 2301400095931 := by
  apply lucas_primality 2301400095931 (3 : ZMod 2301400095931)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (11117, 1), (58979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (11117, 1), (58979, 1)] : List FactorBlock).map factorBlockValue).prod) = 2301400095931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_11117
      · exact prime_ninetyFourCN_58979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2301400095931) ^ 1150700047965 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2301400095931) ^ 767133365310 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2301400095931) ^ 460280019186 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2301400095931) ^ 177030776610 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2301400095931) ^ 207016290 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2301400095931) ^ 39020670 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2632969722287 : Nat.Prime 2632969722287 := by
  apply lucas_primality 2632969722287 (5 : ZMod 2632969722287)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (3977295653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (3977295653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2632969722287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_331
      · exact prime_ninetyFourCN_3977295653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2632969722287) ^ 1316484861143 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2632969722287) ^ 7954591306 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2632969722287) ^ 662 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2918435659729 : Nat.Prime 2918435659729 := by
  apply lucas_primality 2918435659729 (17 : ZMod 2918435659729)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3779, 1), (16089109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3779, 1), (16089109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2918435659729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_3779
      · exact prime_ninetyFourCN_16089109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2918435659729) ^ 1459217829864 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 2918435659729) ^ 972811886576 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 2918435659729) ^ 772277232 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 2918435659729) ^ 181392 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3070623014857 : Nat.Prime 3070623014857 := by
  apply lucas_primality 3070623014857 (5 : ZMod 3070623014857)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (19, 1), (23, 1), (32530543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (19, 1), (23, 1), (32530543, 1)] : List FactorBlock).map factorBlockValue).prod) = 3070623014857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_32530543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3070623014857) ^ 1535311507428 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3070623014857) ^ 1023541004952 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3070623014857) ^ 161611737624 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3070623014857) ^ 133505348472 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3070623014857) ^ 94392 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3096827471329 : Nat.Prime 3096827471329 := by
  apply lucas_primality 3096827471329 (13 : ZMod 3096827471329)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (32258619493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (32258619493, 1)] : List FactorBlock).map factorBlockValue).prod) = 3096827471329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_32258619493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3096827471329) ^ 1548413735664 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3096827471329) ^ 1032275823776 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 3096827471329) ^ 96 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3453983829979 : Nat.Prime 3453983829979 := by
  apply lucas_primality 3453983829979 (3 : ZMod 3453983829979)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (53, 1), (73, 1), (3167, 1), (4271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (53, 1), (73, 1), (3167, 1), (4271, 1)] : List FactorBlock).map factorBlockValue).prod) = 3453983829979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_53
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_3167
      · exact prime_ninetyFourCN_4271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3453983829979) ^ 1726991914989 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3453983829979) ^ 1151327943326 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3453983829979) ^ 313998529998 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3453983829979) ^ 65169506226 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3453983829979) ^ 47314846986 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3453983829979) ^ 1090616934 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3453983829979) ^ 808706118 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3646806491851 : Nat.Prime 3646806491851 := by
  apply lucas_primality 3646806491851 (10 : ZMod 3646806491851)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (24312043279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (24312043279, 1)] : List FactorBlock).map factorBlockValue).prod) = 3646806491851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_24312043279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3646806491851) ^ 1823403245925 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3646806491851) ^ 1215602163950 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3646806491851) ^ 729361298370 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3646806491851) ^ 150 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3860686484771 : Nat.Prime 3860686484771 := by
  apply lucas_primality 3860686484771 (2 : ZMod 3860686484771)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (177173, 1), (2179049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (177173, 1), (2179049, 1)] : List FactorBlock).map factorBlockValue).prod) = 3860686484771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_177173
      · exact prime_ninetyFourCN_2179049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3860686484771) ^ 1930343242385 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3860686484771) ^ 772137296954 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3860686484771) ^ 21790490 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3860686484771) ^ 1771730 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3888609395171 : Nat.Prime 3888609395171 := by
  apply lucas_primality 3888609395171 (6 : ZMod 3888609395171)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (1019, 1), (8119369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (1019, 1), (8119369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3888609395171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_47
      · exact prime_ninetyFourCN_1019
      · exact prime_ninetyFourCN_8119369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3888609395171) ^ 1944304697585 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888609395171) ^ 777721879034 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888609395171) ^ 82736370110 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888609395171) ^ 3816103430 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3888609395171) ^ 478930 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_4286014795109 : Nat.Prime 4286014795109 := by
  apply lucas_primality 4286014795109 (2 : ZMod 4286014795109)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1071503698777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1071503698777, 1)] : List FactorBlock).map factorBlockValue).prod) = 4286014795109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_1071503698777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4286014795109) ^ 2143007397554 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4286014795109) ^ 4 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5236071262069 : Nat.Prime 5236071262069 := by
  apply lucas_primality 5236071262069 (2 : ZMod 5236071262069)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16651, 1), (26204989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16651, 1), (26204989, 1)] : List FactorBlock).map factorBlockValue).prod) = 5236071262069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_16651
      · exact prime_ninetyFourCN_26204989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5236071262069) ^ 2618035631034 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5236071262069) ^ 1745357087356 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5236071262069) ^ 314459868 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5236071262069) ^ 199812 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5289150810521 : Nat.Prime 5289150810521 := by
  apply lucas_primality 5289150810521 (3 : ZMod 5289150810521)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (139, 1), (23099, 1), (41183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (139, 1), (23099, 1), (41183, 1)] : List FactorBlock).map factorBlockValue).prod) = 5289150810521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_139
      · exact prime_ninetyFourCN_23099
      · exact prime_ninetyFourCN_41183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5289150810521) ^ 2644575405260 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5289150810521) ^ 1057830162104 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5289150810521) ^ 38051444680 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5289150810521) ^ 228977480 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5289150810521) ^ 128430440 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5399188505099 : Nat.Prime 5399188505099 := by
  apply lucas_primality 5399188505099 (2 : ZMod 5399188505099)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (733, 1), (3682938953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (733, 1), (3682938953, 1)] : List FactorBlock).map factorBlockValue).prod) = 5399188505099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_733
      · exact prime_ninetyFourCN_3682938953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5399188505099) ^ 2699594252549 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5399188505099) ^ 7365877906 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5399188505099) ^ 1466 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5550567896737 : Nat.Prime 5550567896737 := by
  apply lucas_primality 5550567896737 (13 : ZMod 5550567896737)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (89, 1), (157, 1), (459763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (89, 1), (157, 1), (459763, 1)] : List FactorBlock).map factorBlockValue).prod) = 5550567896737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_89
      · exact prime_ninetyFourCN_157
      · exact prime_ninetyFourCN_459763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5550567896737) ^ 2775283948368 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 5550567896737) ^ 1850189298912 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 5550567896737) ^ 62365931424 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 5550567896737) ^ 35353935648 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 5550567896737) ^ 12072672 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_6104776825811 : Nat.Prime 6104776825811 := by
  apply lucas_primality 6104776825811 (2 : ZMod 6104776825811)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (13499, 1), (3478763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (13499, 1), (3478763, 1)] : List FactorBlock).map factorBlockValue).prod) = 6104776825811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_13499
      · exact prime_ninetyFourCN_3478763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6104776825811) ^ 3052388412905 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6104776825811) ^ 1220955365162 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6104776825811) ^ 469598217370 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6104776825811) ^ 452239190 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6104776825811) ^ 1754870 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_6309731345893 : Nat.Prime 6309731345893 := by
  apply lucas_primality 6309731345893 (5 : ZMod 6309731345893)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (7219, 1), (294887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (7219, 1), (294887, 1)] : List FactorBlock).map factorBlockValue).prod) = 6309731345893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_7219
      · exact prime_ninetyFourCN_294887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6309731345893) ^ 3154865672946 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309731345893) ^ 2103243781964 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309731345893) ^ 485363949684 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309731345893) ^ 332091123468 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309731345893) ^ 874045068 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309731345893) ^ 21397116 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_6863595417923 : Nat.Prime 6863595417923 := by
  apply lucas_primality 6863595417923 (2 : ZMod 6863595417923)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (1861, 1), (12376249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (1861, 1), (12376249, 1)] : List FactorBlock).map factorBlockValue).prod) = 6863595417923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_149
      · exact prime_ninetyFourCN_1861
      · exact prime_ninetyFourCN_12376249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6863595417923) ^ 3431797708961 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6863595417923) ^ 46064398778 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6863595417923) ^ 3688122202 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6863595417923) ^ 554578 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_9244979575691 : Nat.Prime 9244979575691 := by
  apply lucas_primality 9244979575691 (2 : ZMod 9244979575691)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (233, 1), (19079, 1), (207967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (233, 1), (19079, 1), (207967, 1)] : List FactorBlock).map factorBlockValue).prod) = 9244979575691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_233
      · exact prime_ninetyFourCN_19079
      · exact prime_ninetyFourCN_207967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9244979575691) ^ 4622489787845 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9244979575691) ^ 1848995915138 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9244979575691) ^ 39678023930 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9244979575691) ^ 484563110 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9244979575691) ^ 44454070 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_10572616032757 : Nat.Prime 10572616032757 := by
  apply lucas_primality 10572616032757 (5 : ZMod 10572616032757)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (3847385747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (3847385747, 1)] : List FactorBlock).map factorBlockValue).prod) = 10572616032757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_229
      · exact prime_ninetyFourCN_3847385747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10572616032757) ^ 5286308016378 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 10572616032757) ^ 3524205344252 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 10572616032757) ^ 46168628964 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 10572616032757) ^ 2748 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_10928563313917 : Nat.Prime 10928563313917 := by
  apply lucas_primality 10928563313917 (2 : ZMod 10928563313917)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1913, 1), (20698507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1913, 1), (20698507, 1)] : List FactorBlock).map factorBlockValue).prod) = 10928563313917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_1913
      · exact prime_ninetyFourCN_20698507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10928563313917) ^ 5464281656958 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10928563313917) ^ 3642854437972 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10928563313917) ^ 475154926692 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10928563313917) ^ 5712787932 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10928563313917) ^ 527988 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_11698898099611 : Nat.Prime 11698898099611 := by
  apply lucas_primality 11698898099611 (3 : ZMod 11698898099611)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2447, 1), (159363821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2447, 1), (159363821, 1)] : List FactorBlock).map factorBlockValue).prod) = 11698898099611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_2447
      · exact prime_ninetyFourCN_159363821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11698898099611) ^ 5849449049805 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11698898099611) ^ 3899632699870 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11698898099611) ^ 2339779619922 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11698898099611) ^ 4780914630 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11698898099611) ^ 73410 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_11843153058223 : Nat.Prime 11843153058223 := by
  apply lucas_primality 11843153058223 (3 : ZMod 11843153058223)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (657952947679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (657952947679, 1)] : List FactorBlock).map factorBlockValue).prod) = 11843153058223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_657952947679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11843153058223) ^ 5921576529111 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11843153058223) ^ 3947717686074 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 11843153058223) ^ 18 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_13453133665481 : Nat.Prime 13453133665481 := by
  apply lucas_primality 13453133665481 (6 : ZMod 13453133665481)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (336328341637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (336328341637, 1)] : List FactorBlock).map factorBlockValue).prod) = 13453133665481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_336328341637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 13453133665481) ^ 6726566832740 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 13453133665481) ^ 2690626733096 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 13453133665481) ^ 40 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_14408706463831 : Nat.Prime 14408706463831 := by
  apply lucas_primality 14408706463831 (11 : ZMod 14408706463831)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (53, 1), (431527597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (53, 1), (431527597, 1)] : List FactorBlock).map factorBlockValue).prod) = 14408706463831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_53
      · exact prime_ninetyFourCN_431527597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14408706463831) ^ 7204353231915 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 14408706463831) ^ 4802902154610 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 14408706463831) ^ 2881741292766 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 14408706463831) ^ 2058386637690 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 14408706463831) ^ 271862386110 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 14408706463831) ^ 33390 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_18816061778153 : Nat.Prime 18816061778153 := by
  apply lucas_primality 18816061778153 (3 : ZMod 18816061778153)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (124541, 1), (651221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (124541, 1), (651221, 1)] : List FactorBlock).map factorBlockValue).prod) = 18816061778153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_29
      · exact prime_ninetyFourCN_124541
      · exact prime_ninetyFourCN_651221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18816061778153) ^ 9408030889076 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 18816061778153) ^ 648829716488 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 18816061778153) ^ 151083272 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 18816061778153) ^ 28893512 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_19376284792693 : Nat.Prime 19376284792693 := by
  apply lucas_primality 19376284792693 (2 : ZMod 19376284792693)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (127, 1), (229, 1), (760549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (127, 1), (229, 1), (760549, 1)] : List FactorBlock).map factorBlockValue).prod) = 19376284792693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_127
      · exact prime_ninetyFourCN_229
      · exact prime_ninetyFourCN_760549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19376284792693) ^ 9688142396346 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19376284792693) ^ 6458761597564 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19376284792693) ^ 265428558804 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19376284792693) ^ 152569171596 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19376284792693) ^ 84612597348 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 19376284792693) ^ 25476708 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_22460248372729 : Nat.Prime 22460248372729 := by
  apply lucas_primality 22460248372729 (11 : ZMod 22460248372729)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (935843682197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (935843682197, 1)] : List FactorBlock).map factorBlockValue).prod) = 22460248372729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_935843682197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 22460248372729) ^ 11230124186364 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 22460248372729) ^ 7486749457576 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (11 : ZMod 22460248372729) ^ 24 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_23144870777071 : Nat.Prime 23144870777071 := by
  apply lucas_primality 23144870777071 (6 : ZMod 23144870777071)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (5800719493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (5800719493, 1)] : List FactorBlock).map factorBlockValue).prod) = 23144870777071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_5800719493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23144870777071) ^ 11572435388535 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 23144870777071) ^ 7714956925690 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 23144870777071) ^ 4628974155414 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 23144870777071) ^ 3306410111010 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 23144870777071) ^ 1218151093530 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 23144870777071) ^ 3990 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_24254853543523 : Nat.Prime 24254853543523 := by
  apply lucas_primality 24254853543523 (3 : ZMod 24254853543523)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3967, 1), (48525041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3967, 1), (48525041, 1)] : List FactorBlock).map factorBlockValue).prod) = 24254853543523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_3967
      · exact prime_ninetyFourCN_48525041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24254853543523) ^ 12127426771761 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24254853543523) ^ 8084951181174 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24254853543523) ^ 3464979077646 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24254853543523) ^ 6114155166 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24254853543523) ^ 499842 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_27698126313713 : Nat.Prime 27698126313713 := by
  apply lucas_primality 27698126313713 (3 : ZMod 27698126313713)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (439, 1), (5039, 1), (19087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (439, 1), (5039, 1), (19087, 1)] : List FactorBlock).map factorBlockValue).prod) = 27698126313713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_41
      · exact prime_ninetyFourCN_439
      · exact prime_ninetyFourCN_5039
      · exact prime_ninetyFourCN_19087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27698126313713) ^ 13849063156856 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 27698126313713) ^ 675564056432 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 27698126313713) ^ 63093681808 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 27698126313713) ^ 5496750608 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 27698126313713) ^ 1451151376 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_27932663701477 : Nat.Prime 27932663701477 := by
  apply lucas_primality 27932663701477 (2 : ZMod 27932663701477)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (775907325041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (775907325041, 1)] : List FactorBlock).map factorBlockValue).prod) = 27932663701477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_775907325041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27932663701477) ^ 13966331850738 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27932663701477) ^ 9310887900492 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27932663701477) ^ 36 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_37534026874709 : Nat.Prime 37534026874709 := by
  apply lucas_primality 37534026874709 (2 : ZMod 37534026874709)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (491, 1), (210011117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (491, 1), (210011117, 1)] : List FactorBlock).map factorBlockValue).prod) = 37534026874709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_491
      · exact prime_ninetyFourCN_210011117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37534026874709) ^ 18767013437354 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 37534026874709) ^ 5362003839244 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 37534026874709) ^ 2887232836516 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 37534026874709) ^ 76444046588 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 37534026874709) ^ 178724 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_37660850571193 : Nat.Prime 37660850571193 := by
  apply lucas_primality 37660850571193 (13 : ZMod 37660850571193)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (49697, 1), (1372843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (49697, 1), (1372843, 1)] : List FactorBlock).map factorBlockValue).prod) = 37660850571193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_49697
      · exact prime_ninetyFourCN_1372843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 37660850571193) ^ 18830425285596 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 37660850571193) ^ 12553616857064 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 37660850571193) ^ 1637428285704 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 37660850571193) ^ 757809336 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 37660850571193) ^ 27432744 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_46059162048311 : Nat.Prime 46059162048311 := by
  apply lucas_primality 46059162048311 (19 : ZMod 46059162048311)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (40283, 1), (292427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (40283, 1), (292427, 1)] : List FactorBlock).map factorBlockValue).prod) = 46059162048311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_40283
      · exact prime_ninetyFourCN_292427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 46059162048311) ^ 23029581024155 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (19 : ZMod 46059162048311) ^ 9211832409662 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (19 : ZMod 46059162048311) ^ 2709362473430 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (19 : ZMod 46059162048311) ^ 2002572262970 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (19 : ZMod 46059162048311) ^ 1143389570 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (19 : ZMod 46059162048311) ^ 157506530 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_57027957450319 : Nat.Prime 57027957450319 := by
  apply lucas_primality 57027957450319 (3 : ZMod 57027957450319)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (510049, 1), (2070533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (510049, 1), (2070533, 1)] : List FactorBlock).map factorBlockValue).prod) = 57027957450319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_510049
      · exact prime_ninetyFourCN_2070533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57027957450319) ^ 28513978725159 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 57027957450319) ^ 19009319150106 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 57027957450319) ^ 111808782 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 57027957450319) ^ 27542646 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_59719808859437 : Nat.Prime 59719808859437 := by
  apply lucas_primality 59719808859437 (2 : ZMod 59719808859437)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (181, 1), (211, 1), (313, 1), (6679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (181, 1), (211, 1), (313, 1), (6679, 1)] : List FactorBlock).map factorBlockValue).prod) = 59719808859437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_181
      · exact prime_ninetyFourCN_211
      · exact prime_ninetyFourCN_313
      · exact prime_ninetyFourCN_6679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59719808859437) ^ 29859904429718 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59719808859437) ^ 5429073532676 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59719808859437) ^ 3512929932908 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59719808859437) ^ 329943695356 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59719808859437) ^ 283032269476 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59719808859437) ^ 190798111372 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59719808859437) ^ 8941429684 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_143110914698611 : Nat.Prime 143110914698611 := by
  apply lucas_primality 143110914698611 (2 : ZMod 143110914698611)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (31, 1), (2699696561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (31, 1), (2699696561, 1)] : List FactorBlock).map factorBlockValue).prod) = 143110914698611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_31
      · exact prime_ninetyFourCN_2699696561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 143110914698611) ^ 71555457349305 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 143110914698611) ^ 47703638232870 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 143110914698611) ^ 28622182939722 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 143110914698611) ^ 7532153405190 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 143110914698611) ^ 4616481119310 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 143110914698611) ^ 53010 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_161241429076337 : Nat.Prime 161241429076337 := by
  apply lucas_primality 161241429076337 (6 : ZMod 161241429076337)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1439655616753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1439655616753, 1)] : List FactorBlock).map factorBlockValue).prod) = 161241429076337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_1439655616753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 161241429076337) ^ 80620714538168 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 161241429076337) ^ 23034489868048 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 161241429076337) ^ 112 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_183832585406051 : Nat.Prime 183832585406051 := by
  apply lucas_primality 183832585406051 (6 : ZMod 183832585406051)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (75033708329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (75033708329, 1)] : List FactorBlock).map factorBlockValue).prod) = 183832585406051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_75033708329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 183832585406051) ^ 91916292703025 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 183832585406051) ^ 36766517081210 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 183832585406051) ^ 26261797915150 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 183832585406051) ^ 2450 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_198318471310471 : Nat.Prime 198318471310471 := by
  apply lucas_primality 198318471310471 (17 : ZMod 198318471310471)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (23, 1), (5865674987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (23, 1), (5865674987, 1)] : List FactorBlock).map factorBlockValue).prod) = 198318471310471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_5865674987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 198318471310471) ^ 99159235655235 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 198318471310471) ^ 66106157103490 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 198318471310471) ^ 39663694262094 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 198318471310471) ^ 28331210187210 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 198318471310471) ^ 8622542230890 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 198318471310471) ^ 33810 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_242156405978659 : Nat.Prime 242156405978659 := by
  apply lucas_primality 242156405978659 (2 : ZMod 242156405978659)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13453133665481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13453133665481, 1)] : List FactorBlock).map factorBlockValue).prod) = 242156405978659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13453133665481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 242156405978659) ^ 121078202989329 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 242156405978659) ^ 80718801992886 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 242156405978659) ^ 18 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_287073243902741 : Nat.Prime 287073243902741 := by
  apply lucas_primality 287073243902741 (2 : ZMod 287073243902741)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (113, 1), (67189, 1), (1890541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (113, 1), (67189, 1), (1890541, 1)] : List FactorBlock).map factorBlockValue).prod) = 287073243902741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_113
      · exact prime_ninetyFourCN_67189
      · exact prime_ninetyFourCN_1890541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 287073243902741) ^ 143536621951370 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 287073243902741) ^ 57414648780548 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 287073243902741) ^ 2540471184980 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 287073243902741) ^ 4272622660 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 287073243902741) ^ 151847140 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_316984062166621 : Nat.Prime 316984062166621 := by
  apply lucas_primality 316984062166621 (10 : ZMod 316984062166621)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (73, 1), (113, 1), (33707867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (73, 1), (113, 1), (33707867, 1)] : List FactorBlock).map factorBlockValue).prod) = 316984062166621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_113
      · exact prime_ninetyFourCN_33707867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 316984062166621) ^ 158492031083310 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 316984062166621) ^ 105661354055540 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 316984062166621) ^ 63396812433324 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 316984062166621) ^ 16683371692980 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 316984062166621) ^ 4342247426940 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 316984062166621) ^ 2805168691740 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 316984062166621) ^ 9403860 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_318058762179071 : Nat.Prime 318058762179071 := by
  apply lucas_primality 318058762179071 (7 : ZMod 318058762179071)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17, 1), (19, 1), (953, 1), (9393323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17, 1), (19, 1), (953, 1), (9393323, 1)] : List FactorBlock).map factorBlockValue).prod) = 318058762179071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_953
      · exact prime_ninetyFourCN_9393323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 318058762179071) ^ 159029381089535 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 318058762179071) ^ 63611752435814 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 318058762179071) ^ 28914432925370 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 318058762179071) ^ 18709338951710 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 318058762179071) ^ 16739934851530 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 318058762179071) ^ 333744766190 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 318058762179071) ^ 33860090 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_363864364352441 : Nat.Prime 363864364352441 := by
  apply lucas_primality 363864364352441 (3 : ZMod 363864364352441)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (1299515586973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (1299515586973, 1)] : List FactorBlock).map factorBlockValue).prod) = 363864364352441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_1299515586973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 363864364352441) ^ 181932182176220 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 363864364352441) ^ 72772872870488 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 363864364352441) ^ 51980623478920 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 363864364352441) ^ 280 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_428069488762691 : Nat.Prime 428069488762691 := by
  apply lucas_primality 428069488762691 (2 : ZMod 428069488762691)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (14149, 1), (70359067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (14149, 1), (70359067, 1)] : List FactorBlock).map factorBlockValue).prod) = 428069488762691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_43
      · exact prime_ninetyFourCN_14149
      · exact prime_ninetyFourCN_70359067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 428069488762691) ^ 214034744381345 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 428069488762691) ^ 85613897752538 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 428069488762691) ^ 9955104389830 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 428069488762691) ^ 30254398810 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 428069488762691) ^ 6084070 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_727728728704883 : Nat.Prime 727728728704883 := by
  apply lucas_primality 727728728704883 (2 : ZMod 727728728704883)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (363864364352441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (363864364352441, 1)] : List FactorBlock).map factorBlockValue).prod) = 727728728704883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_363864364352441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 727728728704883) ^ 363864364352441 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 727728728704883) ^ 2 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_960442198053571 : Nat.Prime 960442198053571 := by
  apply lucas_primality 960442198053571 (2 : ZMod 960442198053571)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (73, 1), (131, 1), (173, 1), (6450427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (73, 1), (131, 1), (173, 1), (6450427, 1)] : List FactorBlock).map factorBlockValue).prod) = 960442198053571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_131
      · exact prime_ninetyFourCN_173
      · exact prime_ninetyFourCN_6450427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 960442198053571) ^ 480221099026785 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960442198053571) ^ 320147399351190 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960442198053571) ^ 192088439610714 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960442198053571) ^ 13156742439090 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960442198053571) ^ 7331619832470 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960442198053571) ^ 5551689006090 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 960442198053571) ^ 148895910 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1027129620186403 : Nat.Prime 1027129620186403 := by
  apply lucas_primality 1027129620186403 (13 : ZMod 1027129620186403)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (431, 1), (397188561557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (431, 1), (397188561557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1027129620186403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_431
      · exact prime_ninetyFourCN_397188561557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1027129620186403) ^ 513564810093201 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1027129620186403) ^ 342376540062134 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1027129620186403) ^ 2383131369342 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 1027129620186403) ^ 2586 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1027510222604251 : Nat.Prime 1027510222604251 := by
  apply lucas_primality 1027510222604251 (3 : ZMod 1027510222604251)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7, 1), (11, 1), (17, 1), (31, 1), (33761641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7, 1), (11, 1), (17, 1), (31, 1), (33761641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1027510222604251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_31
      · exact prime_ninetyFourCN_33761641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1027510222604251) ^ 513755111302125 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1027510222604251) ^ 342503407534750 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1027510222604251) ^ 205502044520850 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1027510222604251) ^ 146787174657750 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1027510222604251) ^ 93410020236750 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1027510222604251) ^ 60441777800250 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1027510222604251) ^ 33145491051750 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1027510222604251) ^ 30434250 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2101906114912393 : Nat.Prime 2101906114912393 := by
  apply lucas_primality 2101906114912393 (29 : ZMod 2101906114912393)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (709, 1), (1307, 1), (4974239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (709, 1), (1307, 1), (4974239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2101906114912393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_709
      · exact prime_ninetyFourCN_1307
      · exact prime_ninetyFourCN_4974239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 2101906114912393) ^ 1050953057456196 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 2101906114912393) ^ 700635371637464 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 2101906114912393) ^ 110626637626968 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 2101906114912393) ^ 2964606650088 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 2101906114912393) ^ 1608191365656 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 2101906114912393) ^ 422558328 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2438999400162217 : Nat.Prime 2438999400162217 := by
  apply lucas_primality 2438999400162217 (5 : ZMod 2438999400162217)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3359, 1), (30254532601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3359, 1), (30254532601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2438999400162217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_3359
      · exact prime_ninetyFourCN_30254532601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2438999400162217) ^ 1219499700081108 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2438999400162217) ^ 812999800054072 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2438999400162217) ^ 726108782424 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2438999400162217) ^ 80616 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2455101315131713 : Nat.Prime 2455101315131713 := by
  apply lucas_primality 2455101315131713 (5 : ZMod 2455101315131713)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 1), (31, 1), (1439, 1), (22049683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 1), (31, 1), (1439, 1), (22049683, 1)] : List FactorBlock).map factorBlockValue).prod) = 2455101315131713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_31
      · exact prime_ninetyFourCN_1439
      · exact prime_ninetyFourCN_22049683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2455101315131713) ^ 1227550657565856 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2455101315131713) ^ 818367105043904 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2455101315131713) ^ 188853947317824 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2455101315131713) ^ 79196816617152 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2455101315131713) ^ 1706116271808 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2455101315131713) ^ 111344064 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2950891586890277 : Nat.Prime 2950891586890277 := by
  apply lucas_primality 2950891586890277 (2 : ZMod 2950891586890277)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4657, 1), (8923, 1), (17753179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4657, 1), (8923, 1), (17753179, 1)] : List FactorBlock).map factorBlockValue).prod) = 2950891586890277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_4657
      · exact prime_ninetyFourCN_8923
      · exact prime_ninetyFourCN_17753179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2950891586890277) ^ 1475445793445138 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2950891586890277) ^ 633646464868 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2950891586890277) ^ 330706218412 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2950891586890277) ^ 166217644 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3387671201533139 : Nat.Prime 3387671201533139 := by
  apply lucas_primality 3387671201533139 (2 : ZMod 3387671201533139)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1226857, 1), (106202309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1226857, 1), (106202309, 1)] : List FactorBlock).map factorBlockValue).prod) = 3387671201533139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_1226857
      · exact prime_ninetyFourCN_106202309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3387671201533139) ^ 1693835600766569 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3387671201533139) ^ 260590092425626 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3387671201533139) ^ 2761260034 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3387671201533139) ^ 31898282 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3881629930561349 : Nat.Prime 3881629930561349 := by
  apply lucas_primality 3881629930561349 (2 : ZMod 3881629930561349)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (233, 1), (594976997327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (233, 1), (594976997327, 1)] : List FactorBlock).map factorBlockValue).prod) = 3881629930561349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_233
      · exact prime_ninetyFourCN_594976997327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3881629930561349) ^ 1940814965280674 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3881629930561349) ^ 554518561508764 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3881629930561349) ^ 16659355925156 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3881629930561349) ^ 6524 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5906288383613833 : Nat.Prime 5906288383613833 := by
  apply lucas_primality 5906288383613833 (5 : ZMod 5906288383613833)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (5236071262069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (5236071262069, 1)] : List FactorBlock).map factorBlockValue).prod) = 5906288383613833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_47
      · exact prime_ninetyFourCN_5236071262069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5906288383613833) ^ 2953144191806916 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5906288383613833) ^ 1968762794537944 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5906288383613833) ^ 125665710289656 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5906288383613833) ^ 1128 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_5979826848988957 : Nat.Prime 5979826848988957 := by
  apply lucas_primality 5979826848988957 (6 : ZMod 5979826848988957)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (45077, 1), (480645103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (45077, 1), (480645103, 1)] : List FactorBlock).map factorBlockValue).prod) = 5979826848988957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_45077
      · exact prime_ninetyFourCN_480645103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5979826848988957) ^ 2989913424494478 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5979826848988957) ^ 1993275616329652 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5979826848988957) ^ 259992471695172 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5979826848988957) ^ 132658048428 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 5979826848988957) ^ 12441252 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_8373586409866061 : Nat.Prime 8373586409866061 := by
  apply lucas_primality 8373586409866061 (10 : ZMod 8373586409866061)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (6863595417923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (6863595417923, 1)] : List FactorBlock).map factorBlockValue).prod) = 8373586409866061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_61
      · exact prime_ninetyFourCN_6863595417923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 8373586409866061) ^ 4186793204933030 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 8373586409866061) ^ 1674717281973212 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 8373586409866061) ^ 137271908358460 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 8373586409866061) ^ 1220 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_9178996625019157 : Nat.Prime 9178996625019157 := by
  apply lucas_primality 9178996625019157 (2 : ZMod 9178996625019157)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (3096827471329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (3096827471329, 1)] : List FactorBlock).map factorBlockValue).prod) = 9178996625019157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_3096827471329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9178996625019157) ^ 4589498312509578 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9178996625019157) ^ 3059665541673052 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9178996625019157) ^ 706076663463012 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9178996625019157) ^ 483105085527324 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9178996625019157) ^ 2964 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_36094911135832399 : Nat.Prime 36094911135832399 := by
  apply lucas_primality 36094911135832399 (3 : ZMod 36094911135832399)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (569, 1), (10572616032757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (569, 1), (10572616032757, 1)] : List FactorBlock).map factorBlockValue).prod) = 36094911135832399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_569
      · exact prime_ninetyFourCN_10572616032757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 36094911135832399) ^ 18047455567916199 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36094911135832399) ^ 12031637045277466 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36094911135832399) ^ 63435696196542 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 36094911135832399) ^ 3414 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_54281226980775229 : Nat.Prime 54281226980775229 := by
  apply lucas_primality 54281226980775229 (2 : ZMod 54281226980775229)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (22543, 1), (28665443069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (22543, 1), (28665443069, 1)] : List FactorBlock).map factorBlockValue).prod) = 54281226980775229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_22543
      · exact prime_ninetyFourCN_28665443069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54281226980775229) ^ 27140613490387614 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 54281226980775229) ^ 18093742326925076 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 54281226980775229) ^ 7754460997253604 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 54281226980775229) ^ 2407897217796 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 54281226980775229) ^ 1893612 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_68291983204542077 : Nat.Prime 68291983204542077 := by
  apply lucas_primality 68291983204542077 (2 : ZMod 68291983204542077)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2438999400162217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2438999400162217, 1)] : List FactorBlock).map factorBlockValue).prod) = 68291983204542077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_2438999400162217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68291983204542077) ^ 34145991602271038 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 68291983204542077) ^ 9755997600648868 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 68291983204542077) ^ 28 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_88073830018215667 : Nat.Prime 88073830018215667 := by
  apply lucas_primality 88073830018215667 (2 : ZMod 88073830018215667)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (443, 1), (1277, 1), (1493, 1), (643691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (443, 1), (1277, 1), (1493, 1), (643691, 1)] : List FactorBlock).map factorBlockValue).prod) = 88073830018215667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_443
      · exact prime_ninetyFourCN_1277
      · exact prime_ninetyFourCN_1493
      · exact prime_ninetyFourCN_643691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88073830018215667) ^ 44036915009107833 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 88073830018215667) ^ 29357943339405222 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 88073830018215667) ^ 198812257377462 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 88073830018215667) ^ 68969326560858 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 88073830018215667) ^ 58991178846762 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 88073830018215667) ^ 136826256726 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_94982193009573953 : Nat.Prime 94982193009573953 := by
  apply lucas_primality 94982193009573953 (3 : ZMod 94982193009573953)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (103, 1), (14408706463831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (103, 1), (14408706463831, 1)] : List FactorBlock).map factorBlockValue).prod) = 94982193009573953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_103
      · exact prime_ninetyFourCN_14408706463831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94982193009573953) ^ 47491096504786976 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 94982193009573953) ^ 922157213685184 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 94982193009573953) ^ 6592 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_108542243889558277 : Nat.Prime 108542243889558277 := by
  apply lucas_primality 108542243889558277 (5 : ZMod 108542243889558277)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (59, 1), (702991, 1), (1639699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (59, 1), (702991, 1), (1639699, 1)] : List FactorBlock).map factorBlockValue).prod) = 108542243889558277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_59
      · exact prime_ninetyFourCN_702991
      · exact prime_ninetyFourCN_1639699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 108542243889558277) ^ 54271121944779138 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 108542243889558277) ^ 36180747963186092 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 108542243889558277) ^ 15506034841365468 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 108542243889558277) ^ 5712749678397804 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 108542243889558277) ^ 1839699048975564 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 108542243889558277) ^ 154400616636 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 108542243889558277) ^ 66196444524 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_172854597529343651 : Nat.Prime 172854597529343651 := by
  apply lucas_primality 172854597529343651 (2 : ZMod 172854597529343651)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (37, 1), (257, 1), (363559990597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (37, 1), (257, 1), (363559990597, 1)] : List FactorBlock).map factorBlockValue).prod) = 172854597529343651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_257
      · exact prime_ninetyFourCN_363559990597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 172854597529343651) ^ 86427298764671825 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 172854597529343651) ^ 34570919505868730 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 172854597529343651) ^ 4671745879171450 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 172854597529343651) ^ 672585982604450 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 172854597529343651) ^ 475450 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_182056356663012379 : Nat.Prime 182056356663012379 := by
  apply lucas_primality 182056356663012379 (2 : ZMod 182056356663012379)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (198318471310471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (198318471310471, 1)] : List FactorBlock).map factorBlockValue).prod) = 182056356663012379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_198318471310471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 182056356663012379) ^ 91028178331506189 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 182056356663012379) ^ 60685452221004126 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 182056356663012379) ^ 10709197450765434 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 182056356663012379) ^ 918 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_377717303270081123 : Nat.Prime 377717303270081123 := by
  apply lucas_primality 377717303270081123 (5 : ZMod 377717303270081123)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (15013, 1), (187871, 1), (3938771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (15013, 1), (187871, 1), (3938771, 1)] : List FactorBlock).map factorBlockValue).prod) = 377717303270081123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_15013
      · exact prime_ninetyFourCN_187871
      · exact prime_ninetyFourCN_3938771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 377717303270081123) ^ 188858651635040561 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 377717303270081123) ^ 22218664898240066 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 377717303270081123) ^ 25159348782394 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 377717303270081123) ^ 2010514146782 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 377717303270081123) ^ 95897248982 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_819594656786913389 : Nat.Prime 819594656786913389 := by
  apply lucas_primality 819594656786913389 (2 : ZMod 819594656786913389)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (73, 1), (59719808859437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (73, 1), (59719808859437, 1)] : List FactorBlock).map factorBlockValue).prod) = 819594656786913389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_47
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_59719808859437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 819594656786913389) ^ 409797328393456694 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 819594656786913389) ^ 17438184186955604 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 819594656786913389) ^ 11227324065574156 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 819594656786913389) ^ 13724 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1292188947243680833 : Nat.Prime 1292188947243680833 := by
  apply lucas_primality 1292188947243680833 (5 : ZMod 1292188947243680833)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (491, 1), (6337, 1), (2163015313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (491, 1), (6337, 1), (2163015313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1292188947243680833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_491
      · exact prime_ninetyFourCN_6337
      · exact prime_ninetyFourCN_2163015313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1292188947243680833) ^ 646094473621840416 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1292188947243680833) ^ 430729649081226944 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1292188947243680833) ^ 2631749383388352 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1292188947243680833) ^ 203911779587136 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1292188947243680833) ^ 597401664 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1300995610298893549 : Nat.Prime 1300995610298893549 := by
  apply lucas_primality 1300995610298893549 (10 : ZMod 1300995610298893549)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (13, 1), (809, 1), (584777, 1), (652903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (13, 1), (809, 1), (584777, 1), (652903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1300995610298893549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_809
      · exact prime_ninetyFourCN_584777
      · exact prime_ninetyFourCN_652903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1300995610298893549) ^ 650497805149446774 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1300995610298893549) ^ 433665203432964516 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1300995610298893549) ^ 100076585407607196 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1300995610298893549) ^ 1608152793941772 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1300995610298893549) ^ 2224772195724 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1300995610298893549) ^ 1992632305716 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1356125178227060971 : Nat.Prime 1356125178227060971 := by
  apply lucas_primality 1356125178227060971 (3 : ZMod 1356125178227060971)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (19, 1), (43, 1), (233, 1), (911, 1), (9654247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (19, 1), (43, 1), (233, 1), (911, 1), (9654247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1356125178227060971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_43
      · exact prime_ninetyFourCN_233
      · exact prime_ninetyFourCN_911
      · exact prime_ninetyFourCN_9654247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1356125178227060971) ^ 678062589113530485 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1356125178227060971) ^ 452041726075686990 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1356125178227060971) ^ 271225035645412194 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1356125178227060971) ^ 71375009380371630 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1356125178227060971) ^ 31537794842489790 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1356125178227060971) ^ 5820279734880090 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1356125178227060971) ^ 1488611611665270 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1356125178227060971) ^ 140469285510 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1427781796888787083 : Nat.Prime 1427781796888787083 := by
  apply lucas_primality 1427781796888787083 (2 : ZMod 1427781796888787083)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (187909, 1), (422125661561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (187909, 1), (422125661561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1427781796888787083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_187909
      · exact prime_ninetyFourCN_422125661561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1427781796888787083) ^ 713890898444393541 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1427781796888787083) ^ 475927265629595694 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1427781796888787083) ^ 7598261908098 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1427781796888787083) ^ 3382362 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1574745103012234577 : Nat.Prime 1574745103012234577 := by
  apply lucas_primality 1574745103012234577 (3 : ZMod 1574745103012234577)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (149, 1), (1399, 1), (1409, 1), (335100679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (149, 1), (1399, 1), (1409, 1), (335100679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1574745103012234577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_149
      · exact prime_ninetyFourCN_1399
      · exact prime_ninetyFourCN_1409
      · exact prime_ninetyFourCN_335100679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1574745103012234577) ^ 787372551506117288 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1574745103012234577) ^ 10568759080619024 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1574745103012234577) ^ 1125621946399024 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1574745103012234577) ^ 1117633146211664 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1574745103012234577) ^ 4699319344 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1618420632558932569 : Nat.Prime 1618420632558932569 := by
  apply lucas_primality 1618420632558932569 (14 : ZMod 1618420632558932569)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (105629011, 1), (638405987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (105629011, 1), (638405987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1618420632558932569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_105629011
      · exact prime_ninetyFourCN_638405987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1618420632558932569) ^ 809210316279466284 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 1618420632558932569) ^ 539473544186310856 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 1618420632558932569) ^ 15321743688 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (14 : ZMod 1618420632558932569) ^ 2535096264 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2001589913633080949 : Nat.Prime 2001589913633080949 := by
  apply lucas_primality 2001589913633080949 (2 : ZMod 2001589913633080949)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (487, 1), (1027510222604251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (487, 1), (1027510222604251, 1)] : List FactorBlock).map factorBlockValue).prod) = 2001589913633080949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_487
      · exact prime_ninetyFourCN_1027510222604251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2001589913633080949) ^ 1000794956816540474 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2001589913633080949) ^ 4110040890417004 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2001589913633080949) ^ 1948 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2293696673837669557 : Nat.Prime 2293696673837669557 := by
  apply lucas_primality 2293696673837669557 (2 : ZMod 2293696673837669557)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (67, 1), (316984062166621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (67, 1), (316984062166621, 1)] : List FactorBlock).map factorBlockValue).prod) = 2293696673837669557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_67
      · exact prime_ninetyFourCN_316984062166621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2293696673837669557) ^ 1146848336918834778 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2293696673837669557) ^ 764565557945889852 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2293696673837669557) ^ 34234278713995068 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2293696673837669557) ^ 7236 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3796234072088999323 : Nat.Prime 3796234072088999323 := by
  apply lucas_primality 3796234072088999323 (2 : ZMod 3796234072088999323)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (3881629930561349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (3881629930561349, 1)] : List FactorBlock).map factorBlockValue).prod) = 3796234072088999323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_163
      · exact prime_ninetyFourCN_3881629930561349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3796234072088999323) ^ 1898117036044499661 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3796234072088999323) ^ 1265411357362999774 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3796234072088999323) ^ 23289779583368094 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3796234072088999323) ^ 978 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_4061872301571222727 : Nat.Prime 4061872301571222727 := by
  apply lucas_primality 4061872301571222727 (7 : ZMod 4061872301571222727)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (73, 1), (103, 1), (75277, 1), (170865581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (73, 1), (103, 1), (75277, 1), (170865581, 1)] : List FactorBlock).map factorBlockValue).prod) = 4061872301571222727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_103
      · exact prime_ninetyFourCN_75277
      · exact prime_ninetyFourCN_170865581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4061872301571222727) ^ 2030936150785611363 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4061872301571222727) ^ 1353957433857074242 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4061872301571222727) ^ 580267471653031818 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4061872301571222727) ^ 55642086322893462 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4061872301571222727) ^ 39435653413312842 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4061872301571222727) ^ 53959008748638 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4061872301571222727) ^ 23772326046 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_6105993023398446407 : Nat.Prime 6105993023398446407 := by
  apply lucas_primality 6105993023398446407 (5 : ZMod 6105993023398446407)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (17919943, 1), (3962061647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (17919943, 1), (3962061647, 1)] : List FactorBlock).map factorBlockValue).prod) = 6105993023398446407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_43
      · exact prime_ninetyFourCN_17919943
      · exact prime_ninetyFourCN_3962061647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6105993023398446407) ^ 3052996511699223203 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6105993023398446407) ^ 141999837753452242 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6105993023398446407) ^ 340737301642 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 6105993023398446407) ^ 1541115098 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_7402638267867353279 : Nat.Prime 7402638267867353279 := by
  apply lucas_primality 7402638267867353279 (13 : ZMod 7402638267867353279)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (1481, 1), (1733, 1), (27059, 1), (62627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (1481, 1), (1733, 1), (27059, 1), (62627, 1)] : List FactorBlock).map factorBlockValue).prod) = 7402638267867353279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_23
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_1481
      · exact prime_ninetyFourCN_1733
      · exact prime_ninetyFourCN_27059
      · exact prime_ninetyFourCN_62627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7402638267867353279) ^ 3701319133933676639 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 7402638267867353279) ^ 321853837733363186 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 7402638267867353279) ^ 200071304536955494 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 7402638267867353279) ^ 4998405312537038 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 7402638267867353279) ^ 4271574303443366 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 7402638267867353279) ^ 273573977895242 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 7402638267867353279) ^ 118202025769514 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_7816496685231632977 : Nat.Prime 7816496685231632977 := by
  apply lucas_primality 7816496685231632977 (7 : ZMod 7816496685231632977)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (54281226980775229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (54281226980775229, 1)] : List FactorBlock).map factorBlockValue).prod) = 7816496685231632977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_54281226980775229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 7816496685231632977) ^ 3908248342615816488 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 7816496685231632977) ^ 2605498895077210992 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 7816496685231632977) ^ 144 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_9287368490023660649 : Nat.Prime 9287368490023660649 := by
  apply lucas_primality 9287368490023660649 (3 : ZMod 9287368490023660649)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (494353009, 1), (2348364509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (494353009, 1), (2348364509, 1)] : List FactorBlock).map factorBlockValue).prod) = 9287368490023660649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_494353009
      · exact prime_ninetyFourCN_2348364509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9287368490023660649) ^ 4643684245011830324 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9287368490023660649) ^ 18786916072 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9287368490023660649) ^ 3954824072 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_14805276535734706559 : Nat.Prime 14805276535734706559 := by
  apply lucas_primality 14805276535734706559 (13 : ZMod 14805276535734706559)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7402638267867353279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7402638267867353279, 1)] : List FactorBlock).map factorBlockValue).prod) = 14805276535734706559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7402638267867353279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 14805276535734706559) ^ 7402638267867353279 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 14805276535734706559) ^ 2 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_16184206325589325691 : Nat.Prime 16184206325589325691 := by
  apply lucas_primality 16184206325589325691 (6 : ZMod 16184206325589325691)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1618420632558932569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1618420632558932569, 1)] : List FactorBlock).map factorBlockValue).prod) = 16184206325589325691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_1618420632558932569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 16184206325589325691) ^ 8092103162794662845 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 16184206325589325691) ^ 3236841265117865138 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 16184206325589325691) ^ 10 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_41990065740653528977 : Nat.Prime 41990065740653528977 := by
  apply lucas_primality 41990065740653528977 (7 : ZMod 41990065740653528977)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (499, 1), (496163, 1), (3533299051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (499, 1), (496163, 1), (3533299051, 1)] : List FactorBlock).map factorBlockValue).prod) = 41990065740653528977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_499
      · exact prime_ninetyFourCN_496163
      · exact prime_ninetyFourCN_3533299051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 41990065740653528977) ^ 20995032870326764488 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41990065740653528977) ^ 13996688580217842992 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41990065740653528977) ^ 84148428337983024 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41990065740653528977) ^ 84629578869552 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 41990065740653528977) ^ 11884096176 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_51163727187856781119 : Nat.Prime 51163727187856781119 := by
  apply lucas_primality 51163727187856781119 (13 : ZMod 51163727187856781119)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (929, 1), (9178996625019157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (929, 1), (9178996625019157, 1)] : List FactorBlock).map factorBlockValue).prod) = 51163727187856781119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_929
      · exact prime_ninetyFourCN_9178996625019157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 51163727187856781119) ^ 25581863593928390559 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 51163727187856781119) ^ 17054575729285593706 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 51163727187856781119) ^ 55073979750114942 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (13 : ZMod 51163727187856781119) ^ 5574 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_61745379129395774119 : Nat.Prime 61745379129395774119 := by
  apply lucas_primality 61745379129395774119 (3 : ZMod 61745379129395774119)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (56916319, 1), (60269161829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (56916319, 1), (60269161829, 1)] : List FactorBlock).map factorBlockValue).prod) = 61745379129395774119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_56916319
      · exact prime_ninetyFourCN_60269161829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61745379129395774119) ^ 30872689564697887059 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 61745379129395774119) ^ 20581793043131924706 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 61745379129395774119) ^ 1084844912922 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 61745379129395774119) ^ 1024493742 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_104091735848234432477 : Nat.Prime 104091735848234432477 := by
  apply lucas_primality 104091735848234432477 (2 : ZMod 104091735848234432477)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (26959, 1), (9468449, 1), (101946809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (26959, 1), (9468449, 1), (101946809, 1)] : List FactorBlock).map factorBlockValue).prod) = 104091735848234432477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_26959
      · exact prime_ninetyFourCN_9468449
      · exact prime_ninetyFourCN_101946809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104091735848234432477) ^ 52045867924117216238 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 104091735848234432477) ^ 3861112646916964 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 104091735848234432477) ^ 10993536095324 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 104091735848234432477) ^ 1021039666364 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_110426980660843237667 : Nat.Prime 110426980660843237667 := by
  apply lucas_primality 110426980660843237667 (2 : ZMod 110426980660843237667)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (98323, 1), (1379734969453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (98323, 1), (1379734969453, 1)] : List FactorBlock).map factorBlockValue).prod) = 110426980660843237667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_98323
      · exact prime_ninetyFourCN_1379734969453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 110426980660843237667) ^ 55213490330421618833 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 110426980660843237667) ^ 10038816423713021606 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 110426980660843237667) ^ 2984512990833601018 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 110426980660843237667) ^ 1123104265134742 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 110426980660843237667) ^ 80034922 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_155155341030217766201 : Nat.Prime 155155341030217766201 := by
  apply lucas_primality 155155341030217766201 (3 : ZMod 155155341030217766201)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (229, 1), (3387671201533139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (229, 1), (3387671201533139, 1)] : List FactorBlock).map factorBlockValue).prod) = 155155341030217766201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_229
      · exact prime_ninetyFourCN_3387671201533139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 155155341030217766201) ^ 77577670515108883100 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 155155341030217766201) ^ 31031068206043553240 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 155155341030217766201) ^ 677534240306627800 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 155155341030217766201) ^ 45800 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_994022907684315347669 : Nat.Prime 994022907684315347669 := by
  apply lucas_primality 994022907684315347669 (2 : ZMod 994022907684315347669)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (1427, 1), (192737, 1), (2422358971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (1427, 1), (192737, 1), (2422358971, 1)] : List FactorBlock).map factorBlockValue).prod) = 994022907684315347669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_373
      · exact prime_ninetyFourCN_1427
      · exact prime_ninetyFourCN_192737
      · exact prime_ninetyFourCN_2422358971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 994022907684315347669) ^ 497011453842157673834 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 994022907684315347669) ^ 2664940771271622916 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 994022907684315347669) ^ 696582275882491484 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 994022907684315347669) ^ 5157405727412564 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 994022907684315347669) ^ 410353262908 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1025652923336177758333 : Nat.Prime 1025652923336177758333 := by
  apply lucas_primality 1025652923336177758333 (2 : ZMod 1025652923336177758333)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (701, 1), (2707, 1), (23333, 1), (643459277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (701, 1), (2707, 1), (23333, 1), (643459277, 1)] : List FactorBlock).map factorBlockValue).prod) = 1025652923336177758333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_701
      · exact prime_ninetyFourCN_2707
      · exact prime_ninetyFourCN_23333
      · exact prime_ninetyFourCN_643459277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1025652923336177758333) ^ 512826461668088879166 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025652923336177758333) ^ 341884307778725919444 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025652923336177758333) ^ 1463128278653605932 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025652923336177758333) ^ 378889147889241876 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025652923336177758333) ^ 43957181817005004 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025652923336177758333) ^ 1593967108716 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3105786907230944872069 : Nat.Prime 3105786907230944872069 := by
  apply lucas_primality 3105786907230944872069 (2 : ZMod 3105786907230944872069)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (331, 1), (271619, 1), (45694267477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (331, 1), (271619, 1), (45694267477, 1)] : List FactorBlock).map factorBlockValue).prod) = 3105786907230944872069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_331
      · exact prime_ninetyFourCN_271619
      · exact prime_ninetyFourCN_45694267477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3105786907230944872069) ^ 1552893453615472436034 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3105786907230944872069) ^ 1035262302410314957356 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3105786907230944872069) ^ 443683843890134981724 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3105786907230944872069) ^ 9383042015803458828 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3105786907230944872069) ^ 11434350716374572 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3105786907230944872069) ^ 67968852084 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3110662592352044189777 : Nat.Prime 3110662592352044189777 := by
  apply lucas_primality 3110662592352044189777 (3 : ZMod 3110662592352044189777)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (431, 1), (94573, 1), (445799, 1), (10699153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (431, 1), (94573, 1), (445799, 1), (10699153, 1)] : List FactorBlock).map factorBlockValue).prod) = 3110662592352044189777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_431
      · exact prime_ninetyFourCN_94573
      · exact prime_ninetyFourCN_445799
      · exact prime_ninetyFourCN_10699153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3110662592352044189777) ^ 1555331296176022094888 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3110662592352044189777) ^ 7217314599424696496 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3110662592352044189777) ^ 32891656100071312 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3110662592352044189777) ^ 6977724473029424 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3110662592352044189777) ^ 290739144710992 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3275933344778451057641 : Nat.Prime 3275933344778451057641 := by
  apply lucas_primality 3275933344778451057641 (3 : ZMod 3275933344778451057641)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71741, 1), (650483, 1), (1754978047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71741, 1), (650483, 1), (1754978047, 1)] : List FactorBlock).map factorBlockValue).prod) = 3275933344778451057641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_71741
      · exact prime_ninetyFourCN_650483
      · exact prime_ninetyFourCN_1754978047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3275933344778451057641) ^ 1637966672389225528820 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3275933344778451057641) ^ 655186668955690211528 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3275933344778451057641) ^ 45663335397868040 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3275933344778451057641) ^ 5036155202793080 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3275933344778451057641) ^ 1866652036120 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_9531008760228445128203 : Nat.Prime 9531008760228445128203 := by
  apply lucas_primality 9531008760228445128203 (2 : ZMod 9531008760228445128203)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (13553, 1), (37579, 1), (128175598951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (13553, 1), (37579, 1), (128175598951, 1)] : List FactorBlock).map factorBlockValue).prod) = 9531008760228445128203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_13553
      · exact prime_ninetyFourCN_37579
      · exact prime_ninetyFourCN_128175598951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9531008760228445128203) ^ 4765504380114222564101 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9531008760228445128203) ^ 130561763838745823674 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9531008760228445128203) ^ 703239781615025834 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9531008760228445128203) ^ 253625928317103838 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9531008760228445128203) ^ 74358995302 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_16295697340671981511733 : Nat.Prime 16295697340671981511733 := by
  apply lucas_primality 16295697340671981511733 (2 : ZMod 16295697340671981511733)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (1913, 1), (36094911135832399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (1913, 1), (36094911135832399, 1)] : List FactorBlock).map factorBlockValue).prod) = 16295697340671981511733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_59
      · exact prime_ninetyFourCN_1913
      · exact prime_ninetyFourCN_36094911135832399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16295697340671981511733) ^ 8147848670335990755866 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16295697340671981511733) ^ 276198260011389517148 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16295697340671981511733) ^ 8518399028056446164 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 16295697340671981511733) ^ 451468 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_42986467783156374161827 : Nat.Prime 42986467783156374161827 := by
  apply lucas_primality 42986467783156374161827 (3 : ZMod 42986467783156374161827)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (6016807171, 1), (62670161779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (6016807171, 1), (62670161779, 1)] : List FactorBlock).map factorBlockValue).prod) = 42986467783156374161827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_19
      · exact prime_ninetyFourCN_6016807171
      · exact prime_ninetyFourCN_62670161779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42986467783156374161827) ^ 21493233891578187080913 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42986467783156374161827) ^ 14328822594385458053942 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42986467783156374161827) ^ 2262445672797703903254 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42986467783156374161827) ^ 7144398442806 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42986467783156374161827) ^ 685916017494 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_228744210245482683076873 : Nat.Prime 228744210245482683076873 := by
  apply lucas_primality 228744210245482683076873 (5 : ZMod 228744210245482683076873)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (9531008760228445128203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (9531008760228445128203, 1)] : List FactorBlock).map factorBlockValue).prod) = 228744210245482683076873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_9531008760228445128203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 228744210245482683076873) ^ 114372105122741341538436 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 228744210245482683076873) ^ 76248070081827561025624 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 228744210245482683076873) ^ 24 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_736854198723422512422461 : Nat.Prime 736854198723422512422461 := by
  apply lucas_primality 736854198723422512422461 (2 : ZMod 736854198723422512422461)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1594261, 1), (4507043, 1), (5127438301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1594261, 1), (4507043, 1), (5127438301, 1)] : List FactorBlock).map factorBlockValue).prod) = 736854198723422512422461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_1594261
      · exact prime_ninetyFourCN_4507043
      · exact prime_ninetyFourCN_5127438301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 736854198723422512422461) ^ 368427099361711256211230 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 736854198723422512422461) ^ 147370839744684502484492 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 736854198723422512422461) ^ 462191698049078860 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 736854198723422512422461) ^ 163489498263811220 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 736854198723422512422461) ^ 143708057604460 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_785576050284980290428637 : Nat.Prime 785576050284980290428637 := by
  apply lucas_primality 785576050284980290428637 (2 : ZMod 785576050284980290428637)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5595798023, 1), (11698898099611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5595798023, 1), (11698898099611, 1)] : List FactorBlock).map factorBlockValue).prod) = 785576050284980290428637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5595798023
      · exact prime_ninetyFourCN_11698898099611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 785576050284980290428637) ^ 392788025142490145214318 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 785576050284980290428637) ^ 261858683428326763476212 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 785576050284980290428637) ^ 140386777195332 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 785576050284980290428637) ^ 67149576276 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1839099210724586396141987 : Nat.Prime 1839099210724586396141987 := by
  apply lucas_primality 1839099210724586396141987 (2 : ZMod 1839099210724586396141987)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (12625027, 1), (318058762179071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (12625027, 1), (318058762179071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1839099210724586396141987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_229
      · exact prime_ninetyFourCN_12625027
      · exact prime_ninetyFourCN_318058762179071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1839099210724586396141987) ^ 919549605362293198070993 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1839099210724586396141987) ^ 8031000920194700419834 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1839099210724586396141987) ^ 145670913078014518 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1839099210724586396141987) ^ 5782262366 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3191461923659333373903509 : Nat.Prime 3191461923659333373903509 := by
  apply lucas_primality 3191461923659333373903509 (2 : ZMod 3191461923659333373903509)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (73, 1), (271, 1), (1300995610298893549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (73, 1), (271, 1), (1300995610298893549, 1)] : List FactorBlock).map factorBlockValue).prod) = 3191461923659333373903509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_31
      · exact prime_ninetyFourCN_73
      · exact prime_ninetyFourCN_271
      · exact prime_ninetyFourCN_1300995610298893549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3191461923659333373903509) ^ 1595730961829666686951754 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3191461923659333373903509) ^ 102950384634172044319468 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3191461923659333373903509) ^ 43718656488484018820596 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3191461923659333373903509) ^ 11776612264425584405548 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3191461923659333373903509) ^ 2453092 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3206378739344065399482631 : Nat.Prime 3206378739344065399482631 := by
  apply lucas_primality 3206378739344065399482631 (3 : ZMod 3206378739344065399482631)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7219, 1), (14805276535734706559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7219, 1), (14805276535734706559, 1)] : List FactorBlock).map factorBlockValue).prod) = 3206378739344065399482631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_7219
      · exact prime_ninetyFourCN_14805276535734706559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3206378739344065399482631) ^ 1603189369672032699741315 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3206378739344065399482631) ^ 1068792913114688466494210 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3206378739344065399482631) ^ 641275747868813079896526 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3206378739344065399482631) ^ 444158296072041196770 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3206378739344065399482631) ^ 216570 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3878990823932471439653333 : Nat.Prime 3878990823932471439653333 := by
  apply lucas_primality 3878990823932471439653333 (2 : ZMod 3878990823932471439653333)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (241, 1), (659, 1), (6105993023398446407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (241, 1), (659, 1), (6105993023398446407, 1)] : List FactorBlock).map factorBlockValue).prod) = 3878990823932471439653333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_241
      · exact prime_ninetyFourCN_659
      · exact prime_ninetyFourCN_6105993023398446407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3878990823932471439653333) ^ 1939495411966235719826666 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3878990823932471439653333) ^ 16095397609678304728852 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3878990823932471439653333) ^ 5886177274556102336348 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3878990823932471439653333) ^ 635276 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_9149768409819307323074921 : Nat.Prime 9149768409819307323074921 := by
  apply lucas_primality 9149768409819307323074921 (3 : ZMod 9149768409819307323074921)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (228744210245482683076873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (228744210245482683076873, 1)] : List FactorBlock).map factorBlockValue).prod) = 9149768409819307323074921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_228744210245482683076873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9149768409819307323074921) ^ 4574884204909653661537460 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9149768409819307323074921) ^ 1829953681963861464614984 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9149768409819307323074921) ^ 40 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_10488211316125453637794261 : Nat.Prime 10488211316125453637794261 := by
  apply lucas_primality 10488211316125453637794261 (2 : ZMod 10488211316125453637794261)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (131, 1), (46589, 1), (15492173, 1), (205419017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (131, 1), (46589, 1), (15492173, 1), (205419017, 1)] : List FactorBlock).map factorBlockValue).prod) = 10488211316125453637794261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_131
      · exact prime_ninetyFourCN_46589
      · exact prime_ninetyFourCN_15492173
      · exact prime_ninetyFourCN_205419017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10488211316125453637794261) ^ 5244105658062726818897130 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10488211316125453637794261) ^ 3496070438708484545931420 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10488211316125453637794261) ^ 2097642263225090727558852 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10488211316125453637794261) ^ 80062681802484378914460 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10488211316125453637794261) ^ 225122052761927786340 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10488211316125453637794261) ^ 677000658082339620 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 10488211316125453637794261) ^ 51057645340233780 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_13961443103726797329908039 : Nat.Prime 13961443103726797329908039 := by
  apply lucas_primality 13961443103726797329908039 (29 : ZMod 13961443103726797329908039)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (167, 1), (251, 1), (4061872301571222727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (167, 1), (251, 1), (4061872301571222727, 1)] : List FactorBlock).map factorBlockValue).prod) = 13961443103726797329908039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_41
      · exact prime_ninetyFourCN_167
      · exact prime_ninetyFourCN_251
      · exact prime_ninetyFourCN_4061872301571222727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 13961443103726797329908039) ^ 6980721551863398664954019 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 13961443103726797329908039) ^ 340523002529921886095318 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 13961443103726797329908039) ^ 83601455710938906167114 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 13961443103726797329908039) ^ 55623279297716324023538 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (29 : ZMod 13961443103726797329908039) ^ 3437194 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_16352720292181475389356679 : Nat.Prime 16352720292181475389356679 := by
  apply lucas_primality 16352720292181475389356679 (3 : ZMod 16352720292181475389356679)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (1217, 1), (13705589, 1), (2301400095931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (1217, 1), (13705589, 1), (2301400095931, 1)] : List FactorBlock).map factorBlockValue).prod) = 16352720292181475389356679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_71
      · exact prime_ninetyFourCN_1217
      · exact prime_ninetyFourCN_13705589
      · exact prime_ninetyFourCN_2301400095931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16352720292181475389356679) ^ 8176360146090737694678339 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 16352720292181475389356679) ^ 5450906764060491796452226 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 16352720292181475389356679) ^ 230320004115232047737418 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 16352720292181475389356679) ^ 13436910675580505660934 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 16352720292181475389356679) ^ 1193142468534659502 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 16352720292181475389356679) ^ 7105552972338 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_21043947567821493419062297 : Nat.Prime 21043947567821493419062297 := by
  apply lucas_primality 21043947567821493419062297 (10 : ZMod 21043947567821493419062297)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (8629, 1), (7816496685231632977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (8629, 1), (7816496685231632977, 1)] : List FactorBlock).map factorBlockValue).prod) = 21043947567821493419062297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_8629
      · exact prime_ninetyFourCN_7816496685231632977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21043947567821493419062297) ^ 10521973783910746709531148 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 21043947567821493419062297) ^ 7014649189273831139687432 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 21043947567821493419062297) ^ 1618765197524730263004792 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 21043947567821493419062297) ^ 2438746965792269488824 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 21043947567821493419062297) ^ 2692248 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_64462347509086604841106723 : Nat.Prime 64462347509086604841106723 := by
  apply lucas_primality 64462347509086604841106723 (5 : ZMod 64462347509086604841106723)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13108583, 1), (819594656786913389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13108583, 1), (819594656786913389, 1)] : List FactorBlock).map factorBlockValue).prod) = 64462347509086604841106723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13108583
      · exact prime_ninetyFourCN_819594656786913389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64462347509086604841106723) ^ 32231173754543302420553361 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 64462347509086604841106723) ^ 21487449169695534947035574 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 64462347509086604841106723) ^ 4917567940721480334 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 64462347509086604841106723) ^ 78651498 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_125858535793505443653531133 : Nat.Prime 125858535793505443653531133 := by
  apply lucas_primality 125858535793505443653531133 (5 : ZMod 125858535793505443653531133)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10488211316125453637794261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10488211316125453637794261, 1)] : List FactorBlock).map factorBlockValue).prod) = 125858535793505443653531133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_10488211316125453637794261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 125858535793505443653531133) ^ 62929267896752721826765566 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 125858535793505443653531133) ^ 41952845264501814551177044 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 125858535793505443653531133) ^ 12 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_236957541803124321420187613 : Nat.Prime 236957541803124321420187613 := by
  apply lucas_primality 236957541803124321420187613 (2 : ZMod 236957541803124321420187613)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (607, 1), (40961, 1), (653339, 1), (3646806491851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (607, 1), (40961, 1), (653339, 1), (3646806491851, 1)] : List FactorBlock).map factorBlockValue).prod) = 236957541803124321420187613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_607
      · exact prime_ninetyFourCN_40961
      · exact prime_ninetyFourCN_653339
      · exact prime_ninetyFourCN_3646806491851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 236957541803124321420187613) ^ 118478770901562160710093806 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 236957541803124321420187613) ^ 390374862937601847479716 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 236957541803124321420187613) ^ 5784955001174881507292 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 236957541803124321420187613) ^ 362686969250456993108 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 236957541803124321420187613) ^ 64976724795412 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_550163797552798548247861339 : Nat.Prime 550163797552798548247861339 := by
  apply lucas_primality 550163797552798548247861339 (3 : ZMod 550163797552798548247861339)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (367, 1), (1445419, 1), (172854597529343651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (367, 1), (1445419, 1), (172854597529343651, 1)] : List FactorBlock).map factorBlockValue).prod) = 550163797552798548247861339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_367
      · exact prime_ninetyFourCN_1445419
      · exact prime_ninetyFourCN_172854597529343651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 550163797552798548247861339) ^ 275081898776399274123930669 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 550163797552798548247861339) ^ 183387932517599516082620446 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 550163797552798548247861339) ^ 1499083917037598224108614 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 550163797552798548247861339) ^ 380625823759614719502 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 550163797552798548247861339) ^ 3182812638 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_561278217705380337101353487 : Nat.Prime 561278217705380337101353487 := by
  apply lucas_primality 561278217705380337101353487 (5 : ZMod 561278217705380337101353487)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (4182043, 1), (1427781796888787083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (4182043, 1), (1427781796888787083, 1)] : List FactorBlock).map factorBlockValue).prod) = 561278217705380337101353487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_47
      · exact prime_ninetyFourCN_4182043
      · exact prime_ninetyFourCN_1427781796888787083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 561278217705380337101353487) ^ 280639108852690168550676743 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 561278217705380337101353487) ^ 11942089738412347597901138 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 561278217705380337101353487) ^ 134211488907545985802 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (5 : ZMod 561278217705380337101353487) ^ 393112042 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_726360046442256906837045689 : Nat.Prime 726360046442256906837045689 := by
  apply lucas_primality 726360046442256906837045689 (3 : ZMod 726360046442256906837045689)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (181, 1), (271, 1), (4690949, 1), (8000819, 1), (49319531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (181, 1), (271, 1), (4690949, 1), (8000819, 1), (49319531, 1)] : List FactorBlock).map factorBlockValue).prod) = 726360046442256906837045689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_181
      · exact prime_ninetyFourCN_271
      · exact prime_ninetyFourCN_4690949
      · exact prime_ninetyFourCN_8000819
      · exact prime_ninetyFourCN_49319531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 726360046442256906837045689) ^ 363180023221128453418522844 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 726360046442256906837045689) ^ 4013038930620203905177048 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 726360046442256906837045689) ^ 2680295374325671242941128 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 726360046442256906837045689) ^ 154842878582192410712 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 726360046442256906837045689) ^ 90785711618055214952 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 726360046442256906837045689) ^ 14727634908820542248 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_823208052634557827748651781 : Nat.Prime 823208052634557827748651781 := by
  apply lucas_primality 823208052634557827748651781 (6 : ZMod 823208052634557827748651781)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2294403259, 1), (5979826848988957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2294403259, 1), (5979826848988957, 1)] : List FactorBlock).map factorBlockValue).prod) = 823208052634557827748651781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_5
      · exact prime_ninetyFourCN_2294403259
      · exact prime_ninetyFourCN_5979826848988957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 823208052634557827748651781) ^ 411604026317278913874325890 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 823208052634557827748651781) ^ 274402684211519275916217260 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 823208052634557827748651781) ^ 164641610526911565549730356 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 823208052634557827748651781) ^ 358789610939337420 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (6 : ZMod 823208052634557827748651781) ^ 137664195540 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_1157636324017346945271541567 : Nat.Prime 1157636324017346945271541567 := by
  apply lucas_primality 1157636324017346945271541567 (10 : ZMod 1157636324017346945271541567)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (6053, 1), (51163727187856781119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (6053, 1), (51163727187856781119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157636324017346945271541567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_89
      · exact prime_ninetyFourCN_6053
      · exact prime_ninetyFourCN_51163727187856781119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1157636324017346945271541567) ^ 578818162008673472635770783 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1157636324017346945271541567) ^ 385878774672448981757180522 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1157636324017346945271541567) ^ 165376617716763849324505938 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1157636324017346945271541567) ^ 13007149708060078036758894 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1157636324017346945271541567) ^ 191250012228208647822822 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (10 : ZMod 1157636324017346945271541567) ^ 22626114 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_2364533768205644824384425329 : Nat.Prime 2364533768205644824384425329 := by
  apply lucas_primality 2364533768205644824384425329 (3 : ZMod 2364533768205644824384425329)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (23099, 1), (168347, 1), (1027129620186403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (23099, 1), (168347, 1), (1027129620186403, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644824384425329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_37
      · exact prime_ninetyFourCN_23099
      · exact prime_ninetyFourCN_168347
      · exact prime_ninetyFourCN_1027129620186403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2364533768205644824384425329) ^ 1182266884102822412192212664 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2364533768205644824384425329) ^ 63906318059612022280660144 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2364533768205644824384425329) ^ 102365200580356068417872 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2364533768205644824384425329) ^ 14045594921237947955024 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2364533768205644824384425329) ^ 2302079232976 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_3175231060161865907030514013 : Nat.Prime 3175231060161865907030514013 := by
  apply lucas_primality 3175231060161865907030514013 (2 : ZMod 3175231060161865907030514013)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (227, 1), (3023, 1), (3217, 1), (324757, 1), (11905806179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (227, 1), (3023, 1), (3217, 1), (324757, 1), (11905806179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3175231060161865907030514013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_31
      · exact prime_ninetyFourCN_227
      · exact prime_ninetyFourCN_3023
      · exact prime_ninetyFourCN_3217
      · exact prime_ninetyFourCN_324757
      · exact prime_ninetyFourCN_11905806179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3175231060161865907030514013) ^ 1587615530080932953515257006 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175231060161865907030514013) ^ 1058410353387288635676838004 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175231060161865907030514013) ^ 102426808392318255065500452 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175231060161865907030514013) ^ 13987802027144783731411956 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175231060161865907030514013) ^ 1050357611697606982147044 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175231060161865907030514013) ^ 987016182829302426804636 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175231060161865907030514013) ^ 9777252099760331284716 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175231060161865907030514013) ^ 266696014736279028 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_4630545296069387781086166269 : Nat.Prime 4630545296069387781086166269 := by
  apply lucas_primality 4630545296069387781086166269 (2 : ZMod 4630545296069387781086166269)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1157636324017346945271541567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1157636324017346945271541567, 1)] : List FactorBlock).map factorBlockValue).prod) = 4630545296069387781086166269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_1157636324017346945271541567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4630545296069387781086166269) ^ 2315272648034693890543083134 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4630545296069387781086166269) ^ 4 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_4831873352420230728089912627 : Nat.Prime 4831873352420230728089912627 := by
  apply lucas_primality 4831873352420230728089912627 (2 : ZMod 4831873352420230728089912627)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (757, 1), (3191461923659333373903509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (757, 1), (3191461923659333373903509, 1)] : List FactorBlock).map factorBlockValue).prod) = 4831873352420230728089912627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_757
      · exact prime_ninetyFourCN_3191461923659333373903509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4831873352420230728089912627) ^ 2415936676210115364044956313 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4831873352420230728089912627) ^ 6382923847318666747807018 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4831873352420230728089912627) ^ 1514 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_7408872473711020449737866033 : Nat.Prime 7408872473711020449737866033 := by
  apply lucas_primality 7408872473711020449737866033 (7 : ZMod 7408872473711020449737866033)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (573163, 1), (28529971, 1), (726085982341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (573163, 1), (28529971, 1), (726085982341, 1)] : List FactorBlock).map factorBlockValue).prod) = 7408872473711020449737866033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_13
      · exact prime_ninetyFourCN_573163
      · exact prime_ninetyFourCN_28529971
      · exact prime_ninetyFourCN_726085982341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7408872473711020449737866033) ^ 3704436236855510224868933016 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 7408872473711020449737866033) ^ 2469624157903673483245955344 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 7408872473711020449737866033) ^ 569913267208540034595220464 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 7408872473711020449737866033) ^ 12926292300289831077264 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 7408872473711020449737866033) ^ 259687346815425099792 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 7408872473711020449737866033) ^ 10203850031402352 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_7938077650404664767576285029 : Nat.Prime 7938077650404664767576285029 := by
  apply lucas_primality 7938077650404664767576285029 (2 : ZMod 7938077650404664767576285029)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (61, 1), (151, 1), (733, 1), (41990065740653528977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (61, 1), (151, 1), (733, 1), (41990065740653528977, 1)] : List FactorBlock).map factorBlockValue).prod) = 7938077650404664767576285029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_7
      · exact prime_ninetyFourCN_61
      · exact prime_ninetyFourCN_151
      · exact prime_ninetyFourCN_733
      · exact prime_ninetyFourCN_41990065740653528977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7938077650404664767576285029) ^ 3969038825202332383788142514 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7938077650404664767576285029) ^ 1134011092914952109653755004 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7938077650404664767576285029) ^ 130132420498437127337316148 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7938077650404664767576285029) ^ 52570050664931554752160828 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7938077650404664767576285029) ^ 10829573875040470351400116 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7938077650404664767576285029) ^ 189046564 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_18522181184277551124344665079 : Nat.Prime 18522181184277551124344665079 := by
  apply lucas_primality 18522181184277551124344665079 (7 : ZMod 18522181184277551124344665079)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (22460248372729, 1), (24254853543523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (22460248372729, 1), (24254853543523, 1)] : List FactorBlock).map factorBlockValue).prod) = 18522181184277551124344665079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_17
      · exact prime_ninetyFourCN_22460248372729
      · exact prime_ninetyFourCN_24254853543523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 18522181184277551124344665079) ^ 9261090592138775562172332539 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 18522181184277551124344665079) ^ 1089540069663385360255568534 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 18522181184277551124344665079) ^ 824665020479782 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 18522181184277551124344665079) ^ 763648444672786 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_37044362368555102248689330159 : Nat.Prime 37044362368555102248689330159 := by
  apply lucas_primality 37044362368555102248689330159 (17 : ZMod 37044362368555102248689330159)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18522181184277551124344665079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18522181184277551124344665079, 1)] : List FactorBlock).map factorBlockValue).prod) = 37044362368555102248689330159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_18522181184277551124344665079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 37044362368555102248689330159) ^ 18522181184277551124344665079 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (17 : ZMod 37044362368555102248689330159) ^ 2 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_55566543552832653373033995247 : Nat.Prime 55566543552832653373033995247 := by
  apply lucas_primality 55566543552832653373033995247 (3 : ZMod 55566543552832653373033995247)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (283, 1), (127277, 1), (336767, 1), (6309731345893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (283, 1), (127277, 1), (336767, 1), (6309731345893, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832653373033995247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_11
      · exact prime_ninetyFourCN_283
      · exact prime_ninetyFourCN_127277
      · exact prime_ninetyFourCN_336767
      · exact prime_ninetyFourCN_6309731345893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55566543552832653373033995247) ^ 27783271776416326686516997623 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 55566543552832653373033995247) ^ 18522181184277551124344665082 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 55566543552832653373033995247) ^ 5051503959348423033912181386 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 55566543552832653373033995247) ^ 196348210434037644427681962 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 55566543552832653373033995247) ^ 436579614170923681207398 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 55566543552832653373033995247) ^ 164999966008642929304338 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (3 : ZMod 55566543552832653373033995247) ^ 8806483272699222 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_111133087105665306746067990419 : Nat.Prime 111133087105665306746067990419 := by
  apply lucas_primality 111133087105665306746067990419 (2 : ZMod 111133087105665306746067990419)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (2632969722287, 1), (727728728704883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (2632969722287, 1), (727728728704883, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_29
      · exact prime_ninetyFourCN_2632969722287
      · exact prime_ninetyFourCN_727728728704883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111133087105665306746067990419) ^ 55566543552832653373033995209 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 111133087105665306746067990419) ^ 3832175417436734715381654842 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 111133087105665306746067990419) ^ 42208266264883214 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (2 : ZMod 111133087105665306746067990419) ^ 152712243892646 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem prime_ninetyFourCN_111133087105665306746067990487 : Nat.Prime 111133087105665306746067990487 := by
  apply lucas_primality 111133087105665306746067990487 (7 : ZMod 111133087105665306746067990487)
  · rw [← ninetyFourCNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9967, 1), (30097, 1), (61745379129395774119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9967, 1), (30097, 1), (61745379129395774119, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFourCN_2
      · exact prime_ninetyFourCN_3
      · exact prime_ninetyFourCN_9967
      · exact prime_ninetyFourCN_30097
      · exact prime_ninetyFourCN_61745379129395774119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 111133087105665306746067990487) ^ 55566543552832653373033995243 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 111133087105665306746067990487) ^ 37044362368555102248689330162 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 111133087105665306746067990487) ^ 11150104053944547681957258 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 111133087105665306746067990487) ^ 3692497162696126083864438 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide
    · change (7 : ZMod 111133087105665306746067990487) ^ 1799860794 ≠ 1
      rw [← ninetyFourCNFastPow_eq_pow]
      decide

private theorem phi_ninetyFourCN_111133087105665306746067990400 : Nat.totient 111133087105665306746067990400 = 41837031879625093277637672960 := by
  rw [← show ((([(2, 7), (5, 2), (17, 1), (32063, 1), (21831833, 1), (2918435659729, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_17, prime_ninetyFourCN_32063, prime_ninetyFourCN_21831833, prime_ninetyFourCN_2918435659729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990401 : Nat.totient 111133087105665306746067990401 = 111133087105570323383017132032 := by
  rw [← show ((([(1170041284417, 1), (94982193009573953, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_1170041284417, prime_ninetyFourCN_94982193009573953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990402 : Nat.totient 111133087105665306746067990402 = 34182843976541094478740096000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (2861, 1), (2708996369, 1), (183832585406051, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_13, prime_ninetyFourCN_2861, prime_ninetyFourCN_2708996369, prime_ninetyFourCN_183832585406051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990403 : Nat.totient 111133087105665306746067990403 = 110161902490031788715603520000 := by
  rw [← show ((([(137, 1), (691, 1), (332951, 1), (13926889, 1), (253168883431, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_137, prime_ninetyFourCN_691, prime_ninetyFourCN_332951, prime_ninetyFourCN_13926889, prime_ninetyFourCN_253168883431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990404 : Nat.totient 111133087105665306746067990404 = 50116887427976285196932951040 := by
  rw [← show ((([(2, 2), (11, 1), (127, 1), (174679, 1), (520649, 1), (4245079, 1), (51512837, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_11, prime_ninetyFourCN_127, prime_ninetyFourCN_174679, prime_ninetyFourCN_520649, prime_ninetyFourCN_4245079, prime_ninetyFourCN_51512837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990405 : Nat.totient 111133087105665306746067990405 = 57926384476464835707759558656 := by
  rw [← show ((([(3, 1), (5, 1), (53, 1), (257, 1), (126908134643, 1), (4286014795109, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_5, prime_ninetyFourCN_53, prime_ninetyFourCN_257, prime_ninetyFourCN_126908134643, prime_ninetyFourCN_4286014795109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990406 : Nat.totient 111133087105665306746067990406 = 47628465902427988605457710168 := by
  rw [← show ((([(2, 1), (7, 1), (7938077650404664767576285029, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_7, prime_ninetyFourCN_7938077650404664767576285029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990407 : Nat.totient 111133087105665306746067990407 = 111070897028355034049801291064 := by
  rw [← show ((([(1787, 1), (341596159, 1), (182056356663012379, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_1787, prime_ninetyFourCN_341596159, prime_ninetyFourCN_182056356663012379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990408 : Nat.totient 111133087105665306746067990408 = 37041267342874714989748816896 := by
  rw [← show ((([(2, 3), (3, 3), (11969, 1), (42986467783156374161827, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_11969, prime_ninetyFourCN_42986467783156374161827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990409 : Nat.totient 111133087105665306746067990409 = 108659140138790430982679577600 := by
  rw [← show ((([(79, 1), (113, 1), (1279, 1), (14923, 1), (28181, 1), (23144870777071, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_79, prime_ninetyFourCN_113, prime_ninetyFourCN_1279, prime_ninetyFourCN_14923, prime_ninetyFourCN_28181, prime_ninetyFourCN_23144870777071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990410 : Nat.totient 111133087105665306746067990410 = 44453233524788754383044653120 := by
  rw [← show ((([(2, 1), (5, 1), (44394499, 1), (140617229, 1), (1780228230871, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_44394499, prime_ninetyFourCN_140617229, prime_ninetyFourCN_1780228230871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990411 : Nat.totient 111133087105665306746067990411 = 74024197662822989207300812800 := by
  rw [← show ((([(3, 1), (1601, 1), (4057, 1), (41339518439, 1), (137962282519, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_1601, prime_ninetyFourCN_4057, prime_ninetyFourCN_41339518439, prime_ninetyFourCN_137962282519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990412 : Nat.totient 111133087105665306746067990412 = 55565529499393014084618861840 := by
  rw [← show ((([(2, 2), (54799, 1), (1184394767, 1), (428069488762691, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_54799, prime_ninetyFourCN_1184394767, prime_ninetyFourCN_428069488762691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990413 : Nat.totient 111133087105665306746067990413 = 95187541061065668797852784000 := by
  rw [← show ((([(7, 1), (1399, 1), (73141, 1), (155155341030217766201, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_7, prime_ninetyFourCN_1399, prime_ninetyFourCN_73141, prime_ninetyFourCN_155155341030217766201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990414 : Nat.totient 111133087105665306746067990414 = 37027617220203763960014458880 := by
  rw [← show ((([(2, 1), (3, 1), (2213, 1), (6477161, 1), (1292188947243680833, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_2213, prime_ninetyFourCN_6477161, prime_ninetyFourCN_1292188947243680833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990415 : Nat.totient 111133087105665306746067990415 = 70680052041186879729667584000 := by
  rw [← show ((([(5, 1), (11, 1), (13, 1), (19, 1), (1129561, 1), (1862429, 1), (3888609395171, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_5, prime_ninetyFourCN_11, prime_ninetyFourCN_13, prime_ninetyFourCN_19, prime_ninetyFourCN_1129561, prime_ninetyFourCN_1862429, prime_ninetyFourCN_3888609395171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990416 : Nat.totient 111133087105665306746067990416 = 52911826282137053443823635968 := by
  rw [← show ((([(2, 4), (37, 1), (47, 1), (23099, 1), (168347, 1), (1027129620186403, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_37, prime_ninetyFourCN_47, prime_ninetyFourCN_23099, prime_ninetyFourCN_168347, prime_ninetyFourCN_1027129620186403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990417 : Nat.totient 111133087105665306746067990417 = 69730564458456663056356386048 := by
  rw [← show ((([(3, 2), (17, 1), (726360046442256906837045689, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_17, prime_ninetyFourCN_726360046442256906837045689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990418 : Nat.totient 111133087105665306746067990418 = 53650455844093835887787207056 := by
  rw [← show ((([(2, 1), (29, 1), (2632969722287, 1), (727728728704883, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_29, prime_ninetyFourCN_2632969722287, prime_ninetyFourCN_727728728704883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990419 : Nat.totient 111133087105665306746067990419 = 111133087105665306746067990418 := by
  rw [← show ((([(111133087105665306746067990419, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_111133087105665306746067990419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990420 : Nat.totient 111133087105665306746067990420 = 24458364823881784890069319680 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (7, 1), (31, 1), (227, 1), (3023, 1), (3217, 1), (324757, 1), (11905806179, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_5, prime_ninetyFourCN_7, prime_ninetyFourCN_31, prime_ninetyFourCN_227, prime_ninetyFourCN_3023, prime_ninetyFourCN_3217, prime_ninetyFourCN_324757, prime_ninetyFourCN_11905806179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990421 : Nat.totient 111133087105665306746067990421 = 106301213753245076017978077772 := by
  rw [← show ((([(23, 1), (4831873352420230728089912627, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_23, prime_ninetyFourCN_4831873352420230728089912627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990422 : Nat.totient 111133087105665306746067990422 = 54800747714556432093973357440 := by
  rw [← show ((([(2, 1), (83, 1), (571, 1), (308849, 1), (3796234072088999323, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_83, prime_ninetyFourCN_571, prime_ninetyFourCN_308849, prime_ninetyFourCN_3796234072088999323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990423 : Nat.totient 111133087105665306746067990423 = 73983788529528972149591913600 := by
  rw [← show ((([(3, 1), (1187, 1), (1741, 1), (24756515093, 1), (724074284111, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_1187, prime_ninetyFourCN_1741, prime_ninetyFourCN_24756515093, prime_ninetyFourCN_724074284111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990424 : Nat.totient 111133087105665306746067990424 = 54274017680748397728607165440 := by
  rw [← show ((([(2, 3), (43, 1), (193379, 1), (5335143521, 1), (313133490419, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_43, prime_ninetyFourCN_193379, prime_ninetyFourCN_5335143521, prime_ninetyFourCN_313133490419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990425 : Nat.totient 111133087105665306746067990425 = 87907520582632217282933145600 := by
  rw [← show ((([(5, 2), (89, 1), (20344355881, 1), (2455101315131713, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_5, prime_ninetyFourCN_89, prime_ninetyFourCN_20344355881, prime_ninetyFourCN_2455101315131713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990426 : Nat.totient 111133087105665306746067990426 = 33676693062322820226081209160 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (561278217705380337101353487, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_11, prime_ninetyFourCN_561278217705380337101353487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990427 : Nat.totient 111133087105665306746067990427 = 95224118531271790347208547712 := by
  rw [← show ((([(7, 1), (2903, 1), (197445805099, 1), (27698126313713, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_7, prime_ninetyFourCN_2903, prime_ninetyFourCN_197445805099, prime_ninetyFourCN_27698126313713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990428 : Nat.totient 111133087105665306746067990428 = 51249767882588650063447928064 := by
  rw [← show ((([(2, 2), (13, 1), (1319, 1), (14519, 1), (5759543, 1), (19376284792693, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_13, prime_ninetyFourCN_1319, prime_ninetyFourCN_14519, prime_ninetyFourCN_5759543, prime_ninetyFourCN_19376284792693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990429 : Nat.totient 111133087105665306746067990429 = 74032892992010188121497535040 := by
  rw [← show ((([(3, 1), (1327, 1), (97243030349, 1), (287073243902741, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_1327, prime_ninetyFourCN_97243030349, prime_ninetyFourCN_287073243902741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990430 : Nat.totient 111133087105665306746067990430 = 43380503690067177234379473024 := by
  rw [← show ((([(2, 1), (5, 1), (67, 1), (107, 1), (130893311789, 1), (11843153058223, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_67, prime_ninetyFourCN_107, prime_ninetyFourCN_130893311789, prime_ninetyFourCN_11843153058223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990431 : Nat.totient 111133087105665306746067990431 = 111085794720117255941266710400 := by
  rw [← show ((([(2351, 1), (5089769, 1), (9287368490023660649, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2351, prime_ninetyFourCN_5089769, prime_ninetyFourCN_9287368490023660649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990432 : Nat.totient 111133087105665306746067990432 = 37044362368555102248689330112 := by
  rw [← show ((([(2, 5), (3, 1), (1157636324017346945271541567, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_1157636324017346945271541567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990433 : Nat.totient 111133087105665306746067990433 = 108934492185448414921918216000 := by
  rw [← show ((([(71, 1), (173, 1), (1080506591, 1), (8373586409866061, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_71, prime_ninetyFourCN_173, prime_ninetyFourCN_1080506591, prime_ninetyFourCN_8373586409866061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990434 : Nat.totient 111133087105665306746067990434 = 41217022277338158635009310720 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (19, 1), (41, 1), (193, 1), (3105786907230944872069, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_7, prime_ninetyFourCN_17, prime_ninetyFourCN_19, prime_ninetyFourCN_41, prime_ninetyFourCN_193, prime_ninetyFourCN_3105786907230944872069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990435 : Nat.totient 111133087105665306746067990435 = 59270979789688163597902928160 := by
  rw [← show ((([(3, 3), (5, 1), (823208052634557827748651781, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_5, prime_ninetyFourCN_823208052634557827748651781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990436 : Nat.totient 111133087105665306746067990436 = 55562865354411204200241681032 := by
  rw [← show ((([(2, 2), (15107, 1), (1839099210724586396141987, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_15107, prime_ninetyFourCN_1839099210724586396141987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990437 : Nat.totient 111133087105665306746067990437 = 100994504212831813976460121200 := by
  rw [← show ((([(11, 1), (2843, 1), (2620439, 1), (1356125178227060971, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_11, prime_ninetyFourCN_2843, prime_ninetyFourCN_2620439, prime_ninetyFourCN_1356125178227060971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990438 : Nat.totient 111133087105665306746067990438 = 36959978855174139799239964320 := by
  rw [← show ((([(2, 1), (3, 1), (439, 1), (3860686484771, 1), (10928563313917, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_439, prime_ninetyFourCN_3860686484771, prime_ninetyFourCN_10928563313917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990439 : Nat.totient 111133087105665306746067990439 = 111007228569871801302414458424 := by
  rw [← show ((([(883, 1), (125858535793505443653531133, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_883, prime_ninetyFourCN_125858535793505443653531133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990440 : Nat.totient 111133087105665306746067990440 = 44229851752606493941148664384 := by
  rw [← show ((([(2, 3), (5, 1), (199, 1), (13961443103726797329908039, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_199, prime_ninetyFourCN_13961443103726797329908039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990441 : Nat.totient 111133087105665306746067990441 = 58619650341400106304196988928 := by
  rw [← show ((([(3, 1), (7, 3), (13, 1), (1496742987209, 1), (5550567896737, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_7, prime_ninetyFourCN_13, prime_ninetyFourCN_1496742987209, prime_ninetyFourCN_5550567896737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990442 : Nat.totient 111133087105665306746067990442 = 55566526451797007500434707808 := by
  rw [← show ((([(2, 1), (3251447, 1), (4947848617, 1), (3453983829979, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3251447, prime_ninetyFourCN_4947848617, prime_ninetyFourCN_3453983829979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990443 : Nat.totient 111133087105665306746067990443 = 109249469055041694403525648840 := by
  rw [← show ((([(59, 1), (17057531, 1), (110426980660843237667, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_59, prime_ninetyFourCN_17057531, prime_ninetyFourCN_110426980660843237667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990444 : Nat.totient 111133087105665306746067990444 = 35387162142165546604002693120 := by
  rw [← show ((([(2, 2), (3, 2), (23, 1), (761, 1), (2582609, 1), (68291983204542077, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_23, prime_ninetyFourCN_761, prime_ninetyFourCN_2582609, prime_ninetyFourCN_68291983204542077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990445 : Nat.totient 111133087105665306746067990445 = 88070028619628790700613222400 := by
  rw [← show ((([(5, 1), (181, 1), (307, 1), (2557, 1), (4261, 1), (41777, 1), (878773418023, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_5, prime_ninetyFourCN_181, prime_ninetyFourCN_307, prime_ninetyFourCN_2557, prime_ninetyFourCN_4261, prime_ninetyFourCN_41777, prime_ninetyFourCN_878773418023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990446 : Nat.totient 111133087105665306746067990446 = 55566542558809745688662746888 := by
  rw [← show ((([(2, 1), (55900667, 1), (994022907684315347669, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_55900667, prime_ninetyFourCN_994022907684315347669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990447 : Nat.totient 111133087105665306746067990447 = 70825192017417642291173406720 := by
  rw [← show ((([(3, 1), (29, 1), (103, 1), (4973, 1), (4474018459, 1), (557404756561, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_29, prime_ninetyFourCN_103, prime_ninetyFourCN_4973, prime_ninetyFourCN_4474018459, prime_ninetyFourCN_557404756561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990448 : Nat.totient 111133087105665306746067990448 = 43279359451294521409491456000 := by
  rw [← show ((([(2, 4), (7, 1), (11, 1), (2477, 1), (30181, 1), (130517, 1), (9244979575691, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_7, prime_ninetyFourCN_11, prime_ninetyFourCN_2477, prime_ninetyFourCN_30181, prime_ninetyFourCN_130517, prime_ninetyFourCN_9244979575691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990449 : Nat.totient 111133087105665306746067990449 = 111133087105659381641622598464 := by
  rw [← show ((([(18816061778153, 1), (5906288383613833, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_18816061778153, prime_ninetyFourCN_5906288383613833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990450 : Nat.totient 111133087105665306746067990450 = 29480330261886782941365323200 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (191, 1), (3878990823932471439653333, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_5, prime_ninetyFourCN_191, prime_ninetyFourCN_3878990823932471439653333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990451 : Nat.totient 111133087105665306746067990451 = 100669344194293836602256000000 := by
  rw [← show ((([(17, 1), (31, 2), (263, 1), (631, 1), (12979, 1), (14623751, 1), (215966279, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_17, prime_ninetyFourCN_31, prime_ninetyFourCN_263, prime_ninetyFourCN_631, prime_ninetyFourCN_12979, prime_ninetyFourCN_14623751, prime_ninetyFourCN_215966279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990452 : Nat.totient 111133087105665306746067990452 = 55437618857814480163351780920 := by
  rw [← show ((([(2, 2), (431, 1), (64462347509086604841106723, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_431, prime_ninetyFourCN_64462347509086604841106723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990453 : Nat.totient 111133087105665306746067990453 = 67172763290134125973707532800 := by
  rw [← show ((([(3, 2), (19, 1), (37, 1), (61, 1), (299808869, 1), (960442198053571, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_19, prime_ninetyFourCN_37, prime_ninetyFourCN_61, prime_ninetyFourCN_299808869, prime_ninetyFourCN_960442198053571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990454 : Nat.totient 111133087105665306746067990454 = 51280924172007008999559117312 := by
  rw [← show ((([(2, 1), (13, 1), (4603, 1), (404849, 1), (2293696673837669557, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_13, prime_ninetyFourCN_4603, prime_ninetyFourCN_404849, prime_ninetyFourCN_2293696673837669557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990455 : Nat.totient 111133087105665306746067990455 = 76205545443884781768732336288 := by
  rw [← show ((([(5, 1), (7, 1), (3175231060161865907030514013, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_5, prime_ninetyFourCN_7, prime_ninetyFourCN_3175231060161865907030514013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990456 : Nat.totient 111133087105665306746067990456 = 37044362368555102248689330144 := by
  rw [← show ((([(2, 3), (3, 1), (4630545296069387781086166269, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_4630545296069387781086166269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990457 : Nat.totient 111133087105665306746067990457 = 111112043158097485252648922880 := by
  rw [← show ((([(5281, 1), (21043947567821493419062297, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_5281, prime_ninetyFourCN_21043947567821493419062297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990458 : Nat.totient 111133087105665306746067990458 = 54518118202775802815066788416 := by
  rw [← show ((([(2, 1), (53, 1), (27932663701477, 1), (37534026874709, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_53, prime_ninetyFourCN_27932663701477, prime_ninetyFourCN_37534026874709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990459 : Nat.totient 111133087105665306746067990459 = 67353320605978744883120705600 := by
  rw [← show ((([(3, 1), (11, 1), (1028003, 1), (3275933344778451057641, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_11, prime_ninetyFourCN_1028003, prime_ninetyFourCN_3275933344778451057641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990460 : Nat.totient 111133087105665306746067990460 = 44427583812351370175231321280 := by
  rw [← show ((([(2, 2), (5, 1), (1733, 1), (3206378739344065399482631, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_1733, prime_ninetyFourCN_3206378739344065399482631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990461 : Nat.totient 111133087105665306746067990461 = 111133087105662318193630528992 := by
  rw [← show ((([(37660850571193, 1), (2950891586890277, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_37660850571193, prime_ninetyFourCN_2950891586890277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990462 : Nat.totient 111133087105665306746067990462 = 31752293091710094592249462560 := by
  rw [← show ((([(2, 1), (3, 7), (7, 1), (1813391, 1), (2001589913633080949, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_7, prime_ninetyFourCN_1813391, prime_ninetyFourCN_2001589913633080949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990463 : Nat.totient 111133087105665306746067990463 = 108768553337459661921683565088 := by
  rw [← show ((([(47, 1), (2364533768205644824384425329, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_47, prime_ninetyFourCN_2364533768205644824384425329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990464 : Nat.totient 111133087105665306746067990464 = 54680637941907726192832512000 := by
  rw [← show ((([(2, 6), (97, 1), (229, 1), (751, 1), (104091735848234432477, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_97, prime_ninetyFourCN_229, prime_ninetyFourCN_751, prime_ninetyFourCN_104091735848234432477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990465 : Nat.totient 111133087105665306746067990465 = 59178309990813293870405237760 := by
  rw [← show ((([(3, 1), (5, 1), (677, 1), (12479, 1), (210139, 1), (615941, 1), (6775446043, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_5, prime_ninetyFourCN_677, prime_ninetyFourCN_12479, prime_ninetyFourCN_210139, prime_ninetyFourCN_615941, prime_ninetyFourCN_6775446043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990466 : Nat.totient 111133087105665306746067990466 = 55557393784422834065710914240 := by
  rw [← show ((([(2, 1), (6073, 1), (9149768409819307323074921, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_6073, prime_ninetyFourCN_9149768409819307323074921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990467 : Nat.totient 111133087105665306746067990467 = 95842012243636895159448645120 := by
  rw [← show ((([(13, 2), (23, 1), (43, 1), (422231, 1), (1574745103012234577, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_13, prime_ninetyFourCN_23, prime_ninetyFourCN_43, prime_ninetyFourCN_422231, prime_ninetyFourCN_1574745103012234577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990468 : Nat.totient 111133087105665306746067990468 = 34865282229225341761655553024 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (22460248372729, 1), (24254853543523, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_17, prime_ninetyFourCN_22460248372729, prime_ninetyFourCN_24254853543523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990469 : Nat.totient 111133087105665306746067990469 = 95256722983524201714682034352 := by
  rw [← show ((([(7, 1), (456167, 1), (167176426163, 1), (208183563127, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_7, prime_ninetyFourCN_456167, prime_ninetyFourCN_167176426163, prime_ninetyFourCN_208183563127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990470 : Nat.totient 111133087105665306746067990470 = 39743856065627229204442414080 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (73, 1), (349, 1), (104987, 1), (377717303270081123, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_11, prime_ninetyFourCN_73, prime_ninetyFourCN_349, prime_ninetyFourCN_104987, prime_ninetyFourCN_377717303270081123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990471 : Nat.totient 111133087105665306746067990471 = 74088717849289219102293747456 := by
  rw [← show ((([(3, 2), (11085209, 1), (362769263, 1), (3070623014857, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_11085209, prime_ninetyFourCN_362769263, prime_ninetyFourCN_3070623014857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990472 : Nat.totient 111133087105665306746067990472 = 52580989798064280487549131840 := by
  rw [← show ((([(2, 3), (19, 1), (863, 1), (18393863627, 1), (46059162048311, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_19, prime_ninetyFourCN_863, prime_ninetyFourCN_18393863627, prime_ninetyFourCN_46059162048311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990473 : Nat.totient 111133087105665306746067990473 = 111133070809967966074079658960 := by
  rw [← show ((([(6819781, 1), (16295697340671981511733, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_6819781, prime_ninetyFourCN_16295697340671981511733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990474 : Nat.totient 111133087105665306746067990474 = 37044362368555102248689330156 := by
  rw [← show ((([(2, 1), (3, 1), (18522181184277551124344665079, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_18522181184277551124344665079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990475 : Nat.totient 111133087105665306746067990475 = 86725394633979504154133280000 := by
  rw [← show ((([(5, 2), (41, 1), (6871, 1), (110262239, 1), (143110914698611, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_5, prime_ninetyFourCN_41, prime_ninetyFourCN_6871, prime_ninetyFourCN_110262239, prime_ninetyFourCN_143110914698611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990476 : Nat.totient 111133087105665306746067990476 = 45678434442783122379778364160 := by
  rw [← show ((([(2, 2), (7, 1), (29, 2), (163, 1), (1789, 1), (16184206325589325691, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_7, prime_ninetyFourCN_29, prime_ninetyFourCN_163, prime_ninetyFourCN_1789, prime_ninetyFourCN_16184206325589325691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990477 : Nat.totient 111133087105665306746067990477 = 74088724737110204497378660316 := by
  rw [← show ((([(3, 1), (37044362368555102248689330159, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_37044362368555102248689330159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990478 : Nat.totient 111133087105665306746067990478 = 55016379755279854824786133800 := by
  rw [← show ((([(2, 1), (101, 1), (550163797552798548247861339, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_101, prime_ninetyFourCN_550163797552798548247861339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990479 : Nat.totient 111133087105665306746067990479 = 110483415712079628045883367040 := by
  rw [← show ((([(241, 1), (587, 1), (785576050284980290428637, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_241, prime_ninetyFourCN_587, prime_ninetyFourCN_785576050284980290428637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990480 : Nat.totient 111133087105665306746067990480 = 27355788139279837256357990400 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (13, 1), (573163, 1), (28529971, 1), (726085982341, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_5, prime_ninetyFourCN_13, prime_ninetyFourCN_573163, prime_ninetyFourCN_28529971, prime_ninetyFourCN_726085982341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990481 : Nat.totient 111133087105665306746067990481 = 101022710644981226453119266000 := by
  rw [← show ((([(11, 1), (13711, 1), (736854198723422512422461, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_11, prime_ninetyFourCN_13711, prime_ninetyFourCN_736854198723422512422461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990482 : Nat.totient 111133087105665306746067990482 = 53774074405904001142459721760 := by
  rw [← show ((([(2, 1), (31, 1), (852782688127, 1), (2101906114912393, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_31, prime_ninetyFourCN_852782688127, prime_ninetyFourCN_2101906114912393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990483 : Nat.totient 111133087105665306746067990483 = 63492584659880007985392574080 := by
  rw [← show ((([(3, 1), (7, 1), (5279, 1), (9235781, 1), (108542243889558277, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_7, prime_ninetyFourCN_5279, prime_ninetyFourCN_9235781, prime_ninetyFourCN_108542243889558277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990484 : Nat.totient 111133087105665306746067990484 = 55533838112248290422255278488 := by
  rw [← show ((([(2, 2), (1699, 1), (16352720292181475389356679, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_1699, prime_ninetyFourCN_16352720292181475389356679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990485 : Nat.totient 111133087105665306746067990485 = 83676677350132152109580702976 := by
  rw [← show ((([(5, 1), (17, 1), (5399188505099, 1), (242156405978659, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_5, prime_ninetyFourCN_17, prime_ninetyFourCN_5399188505099, prime_ninetyFourCN_242156405978659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990486 : Nat.totient 111133087105665306746067990486 = 37039414958306980282292397696 := by
  rw [← show ((([(2, 1), (3, 1), (9967, 1), (30097, 1), (61745379129395774119, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_9967, prime_ninetyFourCN_30097, prime_ninetyFourCN_61745379129395774119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990487 : Nat.totient 111133087105665306746067990487 = 111133087105665306746067990486 := by
  rw [← show ((([(111133087105665306746067990487, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_111133087105665306746067990487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990488 : Nat.totient 111133087105665306746067990488 = 54432097419833655977882419200 := by
  rw [← show ((([(2, 3), (79, 1), (131, 1), (6529, 1), (14821, 1), (211313, 1), (65645447467, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_79, prime_ninetyFourCN_131, prime_ninetyFourCN_6529, prime_ninetyFourCN_14821, prime_ninetyFourCN_211313, prime_ninetyFourCN_65645447467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990489 : Nat.totient 111133087105665306746067990489 = 74082008614007372460410880000 := by
  rw [← show ((([(3, 3), (17729, 1), (29201, 1), (708016301, 1), (11229344183, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_17729, prime_ninetyFourCN_29201, prime_ninetyFourCN_708016301, prime_ninetyFourCN_11229344183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990490 : Nat.totient 111133087105665306746067990490 = 35376466886749772142662983680 := by
  rw [← show ((([(2, 1), (5, 1), (7, 2), (23, 1), (37, 1), (419, 1), (120259049, 1), (5289150810521, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_7, prime_ninetyFourCN_23, prime_ninetyFourCN_37, prime_ninetyFourCN_419, prime_ninetyFourCN_120259049, prime_ninetyFourCN_5289150810521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990491 : Nat.totient 111133087105665306746067990491 = 104316897310227538841220503040 := by
  rw [← show ((([(19, 1), (109, 1), (91243, 1), (3647431, 1), (161241429076337, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_19, prime_ninetyFourCN_109, prime_ninetyFourCN_91243, prime_ninetyFourCN_3647431, prime_ninetyFourCN_161241429076337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990492 : Nat.totient 111133087105665306746067990492 = 33557330842317795739977653760 := by
  rw [← show ((([(2, 2), (3, 1), (11, 2), (283, 1), (127277, 1), (336767, 1), (6309731345893, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_11, prime_ninetyFourCN_283, prime_ninetyFourCN_127277, prime_ninetyFourCN_336767, prime_ninetyFourCN_6309731345893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990493 : Nat.totient 111133087105665306746067990493 = 102583301874654142336026836736 := by
  rw [← show ((([(13, 1), (94447, 1), (1587172177, 1), (57027957450319, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_13, prime_ninetyFourCN_94447, prime_ninetyFourCN_1587172177, prime_ninetyFourCN_57027957450319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990494 : Nat.totient 111133087105665306746067990494 = 55566543552832653373033995246 := by
  rw [← show ((([(2, 1), (55566543552832653373033995247, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_55566543552832653373033995247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990495 : Nat.totient 111133087105665306746067990495 = 59270979789688163597902928256 := by
  rw [← show ((([(3, 1), (5, 1), (7408872473711020449737866033, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_5, prime_ninetyFourCN_7408872473711020449737866033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990496 : Nat.totient 111133087105665306746067990496 = 55213554278619194471712092160 := by
  rw [← show ((([(2, 5), (167, 1), (3449, 1), (16693, 1), (59167, 1), (6104776825811, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_167, prime_ninetyFourCN_3449, prime_ninetyFourCN_16693, prime_ninetyFourCN_59167, prime_ninetyFourCN_6104776825811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990497 : Nat.totient 111133087105665306746067990497 = 93835186554037231282394294352 := by
  rw [← show ((([(7, 1), (67, 1), (236957541803124321420187613, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_7, prime_ninetyFourCN_67, prime_ninetyFourCN_236957541803124321420187613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990498 : Nat.totient 111133087105665306746067990498 = 37044362368026658847974251672 := by
  rw [← show ((([(2, 1), (3, 2), (70100964083, 1), (88073830018215667, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_3, prime_ninetyFourCN_70100964083, prime_ninetyFourCN_88073830018215667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990499 : Nat.totient 111133087105665306746067990499 = 111098396446839307205639573760 := by
  rw [← show ((([(3583, 1), (30241, 1), (1025652923336177758333, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3583, prime_ninetyFourCN_30241, prime_ninetyFourCN_1025652923336177758333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990500 : Nat.totient 111133087105665306746067990500 = 44452612709747652289574950400 := by
  rw [← show ((([(2, 2), (5, 3), (71453, 1), (3110662592352044189777, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_2, prime_ninetyFourCN_5, prime_ninetyFourCN_71453, prime_ninetyFourCN_3110662592352044189777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFourCN_111133087105665306746067990501 : Nat.totient 111133087105665306746067990501 = 73958511104231142076637309568 := by
  rw [← show ((([(3, 1), (569, 1), (22841563, 1), (42533999, 1), (67011265939, 1)] : List FactorBlock).map factorBlockValue).prod) = 111133087105665306746067990501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFourCN_3, prime_ninetyFourCN_569, prime_ninetyFourCN_22841563, prime_ninetyFourCN_42533999, prime_ninetyFourCN_67011265939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyFourCN : certifiedKill 1 111133087105665306746067990399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyFourCN_111133087105665306746067990400, phi_ninetyFourCN_111133087105665306746067990401, phi_ninetyFourCN_111133087105665306746067990402,
    phi_ninetyFourCN_111133087105665306746067990403, phi_ninetyFourCN_111133087105665306746067990404, phi_ninetyFourCN_111133087105665306746067990405,
    phi_ninetyFourCN_111133087105665306746067990406, phi_ninetyFourCN_111133087105665306746067990407, phi_ninetyFourCN_111133087105665306746067990408,
    phi_ninetyFourCN_111133087105665306746067990409, phi_ninetyFourCN_111133087105665306746067990410, phi_ninetyFourCN_111133087105665306746067990411,
    phi_ninetyFourCN_111133087105665306746067990412, phi_ninetyFourCN_111133087105665306746067990413, phi_ninetyFourCN_111133087105665306746067990414,
    phi_ninetyFourCN_111133087105665306746067990415, phi_ninetyFourCN_111133087105665306746067990416, phi_ninetyFourCN_111133087105665306746067990417,
    phi_ninetyFourCN_111133087105665306746067990418, phi_ninetyFourCN_111133087105665306746067990419, phi_ninetyFourCN_111133087105665306746067990420,
    phi_ninetyFourCN_111133087105665306746067990421, phi_ninetyFourCN_111133087105665306746067990422, phi_ninetyFourCN_111133087105665306746067990423,
    phi_ninetyFourCN_111133087105665306746067990424, phi_ninetyFourCN_111133087105665306746067990425, phi_ninetyFourCN_111133087105665306746067990426,
    phi_ninetyFourCN_111133087105665306746067990427, phi_ninetyFourCN_111133087105665306746067990428, phi_ninetyFourCN_111133087105665306746067990429,
    phi_ninetyFourCN_111133087105665306746067990430, phi_ninetyFourCN_111133087105665306746067990431, phi_ninetyFourCN_111133087105665306746067990432,
    phi_ninetyFourCN_111133087105665306746067990433, phi_ninetyFourCN_111133087105665306746067990434, phi_ninetyFourCN_111133087105665306746067990435,
    phi_ninetyFourCN_111133087105665306746067990436, phi_ninetyFourCN_111133087105665306746067990437, phi_ninetyFourCN_111133087105665306746067990438,
    phi_ninetyFourCN_111133087105665306746067990439, phi_ninetyFourCN_111133087105665306746067990440, phi_ninetyFourCN_111133087105665306746067990441,
    phi_ninetyFourCN_111133087105665306746067990442, phi_ninetyFourCN_111133087105665306746067990443, phi_ninetyFourCN_111133087105665306746067990444,
    phi_ninetyFourCN_111133087105665306746067990445, phi_ninetyFourCN_111133087105665306746067990446, phi_ninetyFourCN_111133087105665306746067990447,
    phi_ninetyFourCN_111133087105665306746067990448, phi_ninetyFourCN_111133087105665306746067990449, phi_ninetyFourCN_111133087105665306746067990450,
    phi_ninetyFourCN_111133087105665306746067990451, phi_ninetyFourCN_111133087105665306746067990452, phi_ninetyFourCN_111133087105665306746067990453,
    phi_ninetyFourCN_111133087105665306746067990454, phi_ninetyFourCN_111133087105665306746067990455, phi_ninetyFourCN_111133087105665306746067990456,
    phi_ninetyFourCN_111133087105665306746067990457, phi_ninetyFourCN_111133087105665306746067990458, phi_ninetyFourCN_111133087105665306746067990459,
    phi_ninetyFourCN_111133087105665306746067990460, phi_ninetyFourCN_111133087105665306746067990461, phi_ninetyFourCN_111133087105665306746067990462,
    phi_ninetyFourCN_111133087105665306746067990463, phi_ninetyFourCN_111133087105665306746067990464, phi_ninetyFourCN_111133087105665306746067990465,
    phi_ninetyFourCN_111133087105665306746067990466, phi_ninetyFourCN_111133087105665306746067990467, phi_ninetyFourCN_111133087105665306746067990468,
    phi_ninetyFourCN_111133087105665306746067990469, phi_ninetyFourCN_111133087105665306746067990470, phi_ninetyFourCN_111133087105665306746067990471,
    phi_ninetyFourCN_111133087105665306746067990472, phi_ninetyFourCN_111133087105665306746067990473, phi_ninetyFourCN_111133087105665306746067990474,
    phi_ninetyFourCN_111133087105665306746067990475, phi_ninetyFourCN_111133087105665306746067990476, phi_ninetyFourCN_111133087105665306746067990477,
    phi_ninetyFourCN_111133087105665306746067990478, phi_ninetyFourCN_111133087105665306746067990479, phi_ninetyFourCN_111133087105665306746067990480,
    phi_ninetyFourCN_111133087105665306746067990481, phi_ninetyFourCN_111133087105665306746067990482, phi_ninetyFourCN_111133087105665306746067990483,
    phi_ninetyFourCN_111133087105665306746067990484, phi_ninetyFourCN_111133087105665306746067990485, phi_ninetyFourCN_111133087105665306746067990486,
    phi_ninetyFourCN_111133087105665306746067990487, phi_ninetyFourCN_111133087105665306746067990488, phi_ninetyFourCN_111133087105665306746067990489,
    phi_ninetyFourCN_111133087105665306746067990490, phi_ninetyFourCN_111133087105665306746067990491, phi_ninetyFourCN_111133087105665306746067990492,
    phi_ninetyFourCN_111133087105665306746067990493, phi_ninetyFourCN_111133087105665306746067990494, phi_ninetyFourCN_111133087105665306746067990495,
    phi_ninetyFourCN_111133087105665306746067990496, phi_ninetyFourCN_111133087105665306746067990497, phi_ninetyFourCN_111133087105665306746067990498,
    phi_ninetyFourCN_111133087105665306746067990499, phi_ninetyFourCN_111133087105665306746067990500, phi_ninetyFourCN_111133087105665306746067990501
    ]

end TotientTailPeriodKiller
end Erdos249257
