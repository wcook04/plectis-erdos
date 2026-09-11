import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtySevenBMFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtySevenBMFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : sixtySevenBMFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtySevenBMFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtySevenBMFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtySevenBMFastPow a n * sixtySevenBMFastPow a n * a else sixtySevenBMFastPow a n * sixtySevenBMFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtySevenBM_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtySevenBM_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtySevenBM_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtySevenBM_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtySevenBM_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtySevenBM_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtySevenBM_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtySevenBM_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtySevenBM_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtySevenBM_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtySevenBM_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtySevenBM_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtySevenBM_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtySevenBM_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtySevenBM_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtySevenBM_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtySevenBM_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtySevenBM_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtySevenBM_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtySevenBM_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtySevenBM_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtySevenBM_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtySevenBM_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtySevenBM_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtySevenBM_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtySevenBM_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtySevenBM_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtySevenBM_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtySevenBM_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtySevenBM_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtySevenBM_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtySevenBM_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtySevenBM_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtySevenBM_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixtySevenBM_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtySevenBM_151 : Nat.Prime 151 := by norm_num
private theorem prime_sixtySevenBM_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixtySevenBM_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtySevenBM_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixtySevenBM_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtySevenBM_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtySevenBM_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixtySevenBM_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixtySevenBM_197 : Nat.Prime 197 := by norm_num
private theorem prime_sixtySevenBM_199 : Nat.Prime 199 := by norm_num
private theorem prime_sixtySevenBM_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtySevenBM_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixtySevenBM_229 : Nat.Prime 229 := by norm_num
private theorem prime_sixtySevenBM_233 : Nat.Prime 233 := by norm_num
private theorem prime_sixtySevenBM_241 : Nat.Prime 241 := by norm_num
private theorem prime_sixtySevenBM_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtySevenBM_257 : Nat.Prime 257 := by norm_num
private theorem prime_sixtySevenBM_263 : Nat.Prime 263 := by norm_num
private theorem prime_sixtySevenBM_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixtySevenBM_271 : Nat.Prime 271 := by norm_num
private theorem prime_sixtySevenBM_277 : Nat.Prime 277 := by norm_num
private theorem prime_sixtySevenBM_293 : Nat.Prime 293 := by norm_num
private theorem prime_sixtySevenBM_307 : Nat.Prime 307 := by norm_num
private theorem prime_sixtySevenBM_311 : Nat.Prime 311 := by norm_num
private theorem prime_sixtySevenBM_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtySevenBM_317 : Nat.Prime 317 := by norm_num
private theorem prime_sixtySevenBM_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtySevenBM_337 : Nat.Prime 337 := by norm_num
private theorem prime_sixtySevenBM_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtySevenBM_349 : Nat.Prime 349 := by norm_num
private theorem prime_sixtySevenBM_353 : Nat.Prime 353 := by norm_num
private theorem prime_sixtySevenBM_359 : Nat.Prime 359 := by norm_num
private theorem prime_sixtySevenBM_373 : Nat.Prime 373 := by norm_num
private theorem prime_sixtySevenBM_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtySevenBM_401 : Nat.Prime 401 := by norm_num
private theorem prime_sixtySevenBM_421 : Nat.Prime 421 := by norm_num
private theorem prime_sixtySevenBM_431 : Nat.Prime 431 := by norm_num
private theorem prime_sixtySevenBM_433 : Nat.Prime 433 := by norm_num
private theorem prime_sixtySevenBM_449 : Nat.Prime 449 := by norm_num
private theorem prime_sixtySevenBM_457 : Nat.Prime 457 := by norm_num
private theorem prime_sixtySevenBM_461 : Nat.Prime 461 := by norm_num
private theorem prime_sixtySevenBM_467 : Nat.Prime 467 := by norm_num
private theorem prime_sixtySevenBM_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixtySevenBM_487 : Nat.Prime 487 := by norm_num
private theorem prime_sixtySevenBM_499 : Nat.Prime 499 := by norm_num
private theorem prime_sixtySevenBM_509 : Nat.Prime 509 := by norm_num
private theorem prime_sixtySevenBM_523 : Nat.Prime 523 := by norm_num
private theorem prime_sixtySevenBM_541 : Nat.Prime 541 := by norm_num
private theorem prime_sixtySevenBM_557 : Nat.Prime 557 := by norm_num
private theorem prime_sixtySevenBM_571 : Nat.Prime 571 := by norm_num
private theorem prime_sixtySevenBM_577 : Nat.Prime 577 := by norm_num
private theorem prime_sixtySevenBM_601 : Nat.Prime 601 := by norm_num
private theorem prime_sixtySevenBM_613 : Nat.Prime 613 := by norm_num
private theorem prime_sixtySevenBM_617 : Nat.Prime 617 := by norm_num
private theorem prime_sixtySevenBM_641 : Nat.Prime 641 := by norm_num
private theorem prime_sixtySevenBM_653 : Nat.Prime 653 := by norm_num
private theorem prime_sixtySevenBM_677 : Nat.Prime 677 := by norm_num
private theorem prime_sixtySevenBM_691 : Nat.Prime 691 := by norm_num
private theorem prime_sixtySevenBM_739 : Nat.Prime 739 := by norm_num
private theorem prime_sixtySevenBM_761 : Nat.Prime 761 := by norm_num
private theorem prime_sixtySevenBM_769 : Nat.Prime 769 := by norm_num
private theorem prime_sixtySevenBM_787 : Nat.Prime 787 := by norm_num
private theorem prime_sixtySevenBM_797 : Nat.Prime 797 := by norm_num
private theorem prime_sixtySevenBM_809 : Nat.Prime 809 := by norm_num
private theorem prime_sixtySevenBM_821 : Nat.Prime 821 := by norm_num
private theorem prime_sixtySevenBM_829 : Nat.Prime 829 := by norm_num
private theorem prime_sixtySevenBM_839 : Nat.Prime 839 := by norm_num
private theorem prime_sixtySevenBM_853 : Nat.Prime 853 := by norm_num
private theorem prime_sixtySevenBM_859 : Nat.Prime 859 := by norm_num
private theorem prime_sixtySevenBM_881 : Nat.Prime 881 := by norm_num
private theorem prime_sixtySevenBM_907 : Nat.Prime 907 := by norm_num
private theorem prime_sixtySevenBM_911 : Nat.Prime 911 := by norm_num
private theorem prime_sixtySevenBM_937 : Nat.Prime 937 := by norm_num
private theorem prime_sixtySevenBM_941 : Nat.Prime 941 := by norm_num
private theorem prime_sixtySevenBM_947 : Nat.Prime 947 := by norm_num
private theorem prime_sixtySevenBM_977 : Nat.Prime 977 := by norm_num
private theorem prime_sixtySevenBM_997 : Nat.Prime 997 := by norm_num
private theorem prime_sixtySevenBM_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_sixtySevenBM_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_sixtySevenBM_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_sixtySevenBM_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_sixtySevenBM_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_sixtySevenBM_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_sixtySevenBM_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_sixtySevenBM_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_sixtySevenBM_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_sixtySevenBM_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_sixtySevenBM_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_sixtySevenBM_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_sixtySevenBM_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_sixtySevenBM_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_sixtySevenBM_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_sixtySevenBM_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_sixtySevenBM_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_sixtySevenBM_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_sixtySevenBM_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_sixtySevenBM_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_sixtySevenBM_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_sixtySevenBM_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_sixtySevenBM_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_sixtySevenBM_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_sixtySevenBM_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_sixtySevenBM_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_sixtySevenBM_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_sixtySevenBM_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_sixtySevenBM_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_sixtySevenBM_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_sixtySevenBM_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_sixtySevenBM_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_sixtySevenBM_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_sixtySevenBM_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_sixtySevenBM_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_sixtySevenBM_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_sixtySevenBM_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_sixtySevenBM_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_sixtySevenBM_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_sixtySevenBM_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_sixtySevenBM_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_sixtySevenBM_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_sixtySevenBM_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_sixtySevenBM_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_sixtySevenBM_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_sixtySevenBM_3251 : Nat.Prime 3251 := by norm_num
private theorem prime_sixtySevenBM_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_sixtySevenBM_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_sixtySevenBM_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_sixtySevenBM_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_sixtySevenBM_3557 : Nat.Prime 3557 := by norm_num
private theorem prime_sixtySevenBM_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_sixtySevenBM_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_sixtySevenBM_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_sixtySevenBM_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_sixtySevenBM_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_sixtySevenBM_4513 : Nat.Prime 4513 := by norm_num
private theorem prime_sixtySevenBM_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_sixtySevenBM_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_sixtySevenBM_4751 : Nat.Prime 4751 := by norm_num
private theorem prime_sixtySevenBM_4799 : Nat.Prime 4799 := by norm_num
private theorem prime_sixtySevenBM_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_sixtySevenBM_4967 : Nat.Prime 4967 := by norm_num
private theorem prime_sixtySevenBM_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_sixtySevenBM_5051 : Nat.Prime 5051 := by norm_num
private theorem prime_sixtySevenBM_5107 : Nat.Prime 5107 := by norm_num
private theorem prime_sixtySevenBM_5689 : Nat.Prime 5689 := by norm_num
private theorem prime_sixtySevenBM_5741 : Nat.Prime 5741 := by norm_num
private theorem prime_sixtySevenBM_5869 : Nat.Prime 5869 := by norm_num
private theorem prime_sixtySevenBM_6037 : Nat.Prime 6037 := by norm_num
private theorem prime_sixtySevenBM_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_sixtySevenBM_6203 : Nat.Prime 6203 := by norm_num
private theorem prime_sixtySevenBM_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_sixtySevenBM_6577 : Nat.Prime 6577 := by norm_num
private theorem prime_sixtySevenBM_6689 : Nat.Prime 6689 := by norm_num
private theorem prime_sixtySevenBM_7079 : Nat.Prime 7079 := by norm_num
private theorem prime_sixtySevenBM_7211 : Nat.Prime 7211 := by norm_num
private theorem prime_sixtySevenBM_7237 : Nat.Prime 7237 := by norm_num
private theorem prime_sixtySevenBM_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_sixtySevenBM_7877 : Nat.Prime 7877 := by norm_num
private theorem prime_sixtySevenBM_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_sixtySevenBM_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_sixtySevenBM_8663 : Nat.Prime 8663 := by norm_num
private theorem prime_sixtySevenBM_9059 : Nat.Prime 9059 := by norm_num
private theorem prime_sixtySevenBM_9431 : Nat.Prime 9431 := by norm_num
private theorem prime_sixtySevenBM_9781 : Nat.Prime 9781 := by norm_num
private theorem prime_sixtySevenBM_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_sixtySevenBM_10169 : Nat.Prime 10169 := by norm_num
private theorem prime_sixtySevenBM_10357 : Nat.Prime 10357 := by norm_num
private theorem prime_sixtySevenBM_10477 : Nat.Prime 10477 := by norm_num
private theorem prime_sixtySevenBM_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_sixtySevenBM_10753 : Nat.Prime 10753 := by norm_num
private theorem prime_sixtySevenBM_11587 : Nat.Prime 11587 := by norm_num
private theorem prime_sixtySevenBM_12577 : Nat.Prime 12577 := by norm_num
private theorem prime_sixtySevenBM_12899 : Nat.Prime 12899 := by norm_num
private theorem prime_sixtySevenBM_13177 : Nat.Prime 13177 := by norm_num
private theorem prime_sixtySevenBM_13339 : Nat.Prime 13339 := by norm_num
private theorem prime_sixtySevenBM_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_sixtySevenBM_13913 : Nat.Prime 13913 := by norm_num
private theorem prime_sixtySevenBM_14159 : Nat.Prime 14159 := by norm_num
private theorem prime_sixtySevenBM_15473 : Nat.Prime 15473 := by norm_num
private theorem prime_sixtySevenBM_15739 : Nat.Prime 15739 := by norm_num
private theorem prime_sixtySevenBM_16057 : Nat.Prime 16057 := by norm_num
private theorem prime_sixtySevenBM_16633 : Nat.Prime 16633 := by norm_num
private theorem prime_sixtySevenBM_17077 : Nat.Prime 17077 := by norm_num
private theorem prime_sixtySevenBM_17183 : Nat.Prime 17183 := by norm_num
private theorem prime_sixtySevenBM_17333 : Nat.Prime 17333 := by norm_num
private theorem prime_sixtySevenBM_17569 : Nat.Prime 17569 := by norm_num
private theorem prime_sixtySevenBM_17747 : Nat.Prime 17747 := by norm_num
private theorem prime_sixtySevenBM_18523 : Nat.Prime 18523 := by norm_num
private theorem prime_sixtySevenBM_19919 : Nat.Prime 19919 := by norm_num
private theorem prime_sixtySevenBM_19963 : Nat.Prime 19963 := by norm_num
private theorem prime_sixtySevenBM_20023 : Nat.Prime 20023 := by norm_num
private theorem prime_sixtySevenBM_20693 : Nat.Prime 20693 := by norm_num
private theorem prime_sixtySevenBM_20707 : Nat.Prime 20707 := by norm_num
private theorem prime_sixtySevenBM_21799 : Nat.Prime 21799 := by norm_num
private theorem prime_sixtySevenBM_24281 : Nat.Prime 24281 := by norm_num
private theorem prime_sixtySevenBM_24859 : Nat.Prime 24859 := by norm_num
private theorem prime_sixtySevenBM_25321 : Nat.Prime 25321 := by norm_num
private theorem prime_sixtySevenBM_25703 : Nat.Prime 25703 := by norm_num
private theorem prime_sixtySevenBM_26357 : Nat.Prime 26357 := by norm_num
private theorem prime_sixtySevenBM_26681 : Nat.Prime 26681 := by norm_num
private theorem prime_sixtySevenBM_26891 : Nat.Prime 26891 := by norm_num
private theorem prime_sixtySevenBM_27067 : Nat.Prime 27067 := by norm_num
private theorem prime_sixtySevenBM_28927 : Nat.Prime 28927 := by norm_num
private theorem prime_sixtySevenBM_29017 : Nat.Prime 29017 := by norm_num
private theorem prime_sixtySevenBM_31319 : Nat.Prime 31319 := by norm_num
private theorem prime_sixtySevenBM_31667 : Nat.Prime 31667 := by norm_num
private theorem prime_sixtySevenBM_32213 : Nat.Prime 32213 := by norm_num
private theorem prime_sixtySevenBM_32609 : Nat.Prime 32609 := by norm_num
private theorem prime_sixtySevenBM_32831 : Nat.Prime 32831 := by norm_num
private theorem prime_sixtySevenBM_33391 : Nat.Prime 33391 := by norm_num
private theorem prime_sixtySevenBM_34613 : Nat.Prime 34613 := by norm_num
private theorem prime_sixtySevenBM_36913 : Nat.Prime 36913 := by norm_num
private theorem prime_sixtySevenBM_37337 : Nat.Prime 37337 := by norm_num
private theorem prime_sixtySevenBM_39667 : Nat.Prime 39667 := by norm_num
private theorem prime_sixtySevenBM_40591 : Nat.Prime 40591 := by norm_num
private theorem prime_sixtySevenBM_40897 : Nat.Prime 40897 := by norm_num
private theorem prime_sixtySevenBM_41941 : Nat.Prime 41941 := by norm_num
private theorem prime_sixtySevenBM_44531 : Nat.Prime 44531 := by norm_num
private theorem prime_sixtySevenBM_47809 : Nat.Prime 47809 := by norm_num
private theorem prime_sixtySevenBM_48787 : Nat.Prime 48787 := by norm_num
private theorem prime_sixtySevenBM_49547 : Nat.Prime 49547 := by norm_num
private theorem prime_sixtySevenBM_52369 : Nat.Prime 52369 := by norm_num
private theorem prime_sixtySevenBM_52733 : Nat.Prime 52733 := by norm_num
private theorem prime_sixtySevenBM_54647 : Nat.Prime 54647 := by norm_num
private theorem prime_sixtySevenBM_55219 : Nat.Prime 55219 := by norm_num
private theorem prime_sixtySevenBM_55291 : Nat.Prime 55291 := by norm_num
private theorem prime_sixtySevenBM_56401 : Nat.Prime 56401 := by norm_num
private theorem prime_sixtySevenBM_57791 : Nat.Prime 57791 := by norm_num
private theorem prime_sixtySevenBM_58153 : Nat.Prime 58153 := by norm_num
private theorem prime_sixtySevenBM_59281 : Nat.Prime 59281 := by norm_num
private theorem prime_sixtySevenBM_60293 : Nat.Prime 60293 := by norm_num
private theorem prime_sixtySevenBM_60539 : Nat.Prime 60539 := by norm_num
private theorem prime_sixtySevenBM_60589 : Nat.Prime 60589 := by norm_num
private theorem prime_sixtySevenBM_63337 : Nat.Prime 63337 := by norm_num
private theorem prime_sixtySevenBM_63929 : Nat.Prime 63929 := by norm_num
private theorem prime_sixtySevenBM_66067 : Nat.Prime 66067 := by norm_num
private theorem prime_sixtySevenBM_66853 : Nat.Prime 66853 := by norm_num
private theorem prime_sixtySevenBM_67511 : Nat.Prime 67511 := by norm_num
private theorem prime_sixtySevenBM_69371 : Nat.Prime 69371 := by norm_num
private theorem prime_sixtySevenBM_71597 : Nat.Prime 71597 := by norm_num
private theorem prime_sixtySevenBM_77743 : Nat.Prime 77743 := by norm_num
private theorem prime_sixtySevenBM_80167 : Nat.Prime 80167 := by norm_num
private theorem prime_sixtySevenBM_83227 : Nat.Prime 83227 := by norm_num
private theorem prime_sixtySevenBM_83653 : Nat.Prime 83653 := by norm_num
private theorem prime_sixtySevenBM_85081 : Nat.Prime 85081 := by norm_num
private theorem prime_sixtySevenBM_89597 : Nat.Prime 89597 := by norm_num
private theorem prime_sixtySevenBM_90397 : Nat.Prime 90397 := by norm_num
private theorem prime_sixtySevenBM_91811 : Nat.Prime 91811 := by norm_num
private theorem prime_sixtySevenBM_91909 : Nat.Prime 91909 := by norm_num
private theorem prime_sixtySevenBM_92357 : Nat.Prime 92357 := by norm_num
private theorem prime_sixtySevenBM_92831 : Nat.Prime 92831 := by norm_num
private theorem prime_sixtySevenBM_96827 : Nat.Prime 96827 := by norm_num
private theorem prime_sixtySevenBM_97187 : Nat.Prime 97187 := by norm_num
private theorem prime_sixtySevenBM_97777 : Nat.Prime 97777 := by norm_num
private theorem prime_sixtySevenBM_101627 : Nat.Prime 101627 := by norm_num
private theorem prime_sixtySevenBM_105733 : Nat.Prime 105733 := by norm_num
private theorem prime_sixtySevenBM_112061 : Nat.Prime 112061 := by norm_num
private theorem prime_sixtySevenBM_114083 : Nat.Prime 114083 := by norm_num
private theorem prime_sixtySevenBM_114487 : Nat.Prime 114487 := by norm_num
private theorem prime_sixtySevenBM_121013 : Nat.Prime 121013 := by norm_num
private theorem prime_sixtySevenBM_124339 : Nat.Prime 124339 := by norm_num
private theorem prime_sixtySevenBM_134129 : Nat.Prime 134129 := by norm_num
private theorem prime_sixtySevenBM_142601 : Nat.Prime 142601 := by norm_num
private theorem prime_sixtySevenBM_160739 : Nat.Prime 160739 := by norm_num
private theorem prime_sixtySevenBM_161641 : Nat.Prime 161641 := by norm_num
private theorem prime_sixtySevenBM_163351 : Nat.Prime 163351 := by norm_num
private theorem prime_sixtySevenBM_167117 : Nat.Prime 167117 := by norm_num
private theorem prime_sixtySevenBM_176087 : Nat.Prime 176087 := by norm_num
private theorem prime_sixtySevenBM_176417 : Nat.Prime 176417 := by norm_num
private theorem prime_sixtySevenBM_192013 : Nat.Prime 192013 := by norm_num
private theorem prime_sixtySevenBM_192121 : Nat.Prime 192121 := by norm_num
private theorem prime_sixtySevenBM_210499 : Nat.Prime 210499 := by norm_num
private theorem prime_sixtySevenBM_215507 : Nat.Prime 215507 := by norm_num
private theorem prime_sixtySevenBM_216551 : Nat.Prime 216551 := by norm_num
private theorem prime_sixtySevenBM_235979 : Nat.Prime 235979 := by norm_num
private theorem prime_sixtySevenBM_245753 : Nat.Prime 245753 := by norm_num
private theorem prime_sixtySevenBM_247439 : Nat.Prime 247439 := by norm_num
private theorem prime_sixtySevenBM_249973 : Nat.Prime 249973 := by norm_num
private theorem prime_sixtySevenBM_249989 : Nat.Prime 249989 := by norm_num
private theorem prime_sixtySevenBM_251263 : Nat.Prime 251263 := by norm_num
private theorem prime_sixtySevenBM_256031 : Nat.Prime 256031 := by norm_num
private theorem prime_sixtySevenBM_258403 : Nat.Prime 258403 := by norm_num
private theorem prime_sixtySevenBM_268253 : Nat.Prime 268253 := by norm_num
private theorem prime_sixtySevenBM_285463 : Nat.Prime 285463 := by norm_num
private theorem prime_sixtySevenBM_296749 : Nat.Prime 296749 := by norm_num
private theorem prime_sixtySevenBM_299371 : Nat.Prime 299371 := by norm_num
private theorem prime_sixtySevenBM_304849 : Nat.Prime 304849 := by norm_num
private theorem prime_sixtySevenBM_329683 : Nat.Prime 329683 := by norm_num
private theorem prime_sixtySevenBM_378149 : Nat.Prime 378149 := by norm_num
private theorem prime_sixtySevenBM_379693 : Nat.Prime 379693 := by norm_num
private theorem prime_sixtySevenBM_460127 : Nat.Prime 460127 := by norm_num
private theorem prime_sixtySevenBM_463237 : Nat.Prime 463237 := by norm_num
private theorem prime_sixtySevenBM_470521 : Nat.Prime 470521 := by norm_num
private theorem prime_sixtySevenBM_510581 : Nat.Prime 510581 := by norm_num
private theorem prime_sixtySevenBM_517511 : Nat.Prime 517511 := by norm_num
private theorem prime_sixtySevenBM_542281 : Nat.Prime 542281 := by norm_num
private theorem prime_sixtySevenBM_546841 : Nat.Prime 546841 := by norm_num
private theorem prime_sixtySevenBM_576049 : Nat.Prime 576049 := by norm_num
private theorem prime_sixtySevenBM_763493 : Nat.Prime 763493 := by norm_num
private theorem prime_sixtySevenBM_818659 : Nat.Prime 818659 := by norm_num
private theorem prime_sixtySevenBM_827147 : Nat.Prime 827147 := by norm_num
private theorem prime_sixtySevenBM_856813 : Nat.Prime 856813 := by norm_num
private theorem prime_sixtySevenBM_887903 : Nat.Prime 887903 := by norm_num
private theorem prime_sixtySevenBM_908533 : Nat.Prime 908533 := by norm_num
private theorem prime_sixtySevenBM_911077 : Nat.Prime 911077 := by norm_num
private theorem prime_sixtySevenBM_940981 : Nat.Prime 940981 := by norm_num
private theorem prime_sixtySevenBM_961487 : Nat.Prime 961487 := by norm_num
private theorem prime_sixtySevenBM_973421 : Nat.Prime 973421 := by norm_num
private theorem prime_sixtySevenBM_980293 : Nat.Prime 980293 := by norm_num
private theorem prime_sixtySevenBM_983441 : Nat.Prime 983441 := by norm_num
private theorem prime_sixtySevenBM_1005287 : Nat.Prime 1005287 := by norm_num
private theorem prime_sixtySevenBM_1061759 : Nat.Prime 1061759 := by norm_num
private theorem prime_sixtySevenBM_1109891 : Nat.Prime 1109891 := by norm_num
private theorem prime_sixtySevenBM_1153871 : Nat.Prime 1153871 := by norm_num
private theorem prime_sixtySevenBM_1162859 : Nat.Prime 1162859 := by norm_num
private theorem prime_sixtySevenBM_1259393 : Nat.Prime 1259393 := by norm_num
private theorem prime_sixtySevenBM_1294393 : Nat.Prime 1294393 := by norm_num
private theorem prime_sixtySevenBM_1299029 : Nat.Prime 1299029 := by norm_num
private theorem prime_sixtySevenBM_1305581 : Nat.Prime 1305581 := by norm_num
private theorem prime_sixtySevenBM_1370321 : Nat.Prime 1370321 := by norm_num
private theorem prime_sixtySevenBM_1378969 : Nat.Prime 1378969 := by norm_num
private theorem prime_sixtySevenBM_1392473 : Nat.Prime 1392473 := by norm_num
private theorem prime_sixtySevenBM_1413781 : Nat.Prime 1413781 := by norm_num
private theorem prime_sixtySevenBM_1452079 : Nat.Prime 1452079 := by norm_num
private theorem prime_sixtySevenBM_1454209 : Nat.Prime 1454209 := by norm_num
private theorem prime_sixtySevenBM_1477519 : Nat.Prime 1477519 := by norm_num
private theorem prime_sixtySevenBM_1636867 : Nat.Prime 1636867 := by norm_num
private theorem prime_sixtySevenBM_1676621 : Nat.Prime 1676621 := by norm_num
private theorem prime_sixtySevenBM_1717621 : Nat.Prime 1717621 := by norm_num
private theorem prime_sixtySevenBM_1721371 : Nat.Prime 1721371 := by norm_num
private theorem prime_sixtySevenBM_1765597 : Nat.Prime 1765597 := by norm_num
private theorem prime_sixtySevenBM_1857521 : Nat.Prime 1857521 := by norm_num
private theorem prime_sixtySevenBM_1857967 : Nat.Prime 1857967 := by norm_num
private theorem prime_sixtySevenBM_1876109 : Nat.Prime 1876109 := by norm_num
private theorem prime_sixtySevenBM_1937153 : Nat.Prime 1937153 := by norm_num
private theorem prime_sixtySevenBM_2019769 : Nat.Prime 2019769 := by norm_num
private theorem prime_sixtySevenBM_2046349 : Nat.Prime 2046349 := by norm_num
private theorem prime_sixtySevenBM_2070323 : Nat.Prime 2070323 := by norm_num
private theorem prime_sixtySevenBM_2077073 : Nat.Prime 2077073 := by norm_num
private theorem prime_sixtySevenBM_2352761 : Nat.Prime 2352761 := by norm_num
private theorem prime_sixtySevenBM_2392147 : Nat.Prime 2392147 := by norm_num
private theorem prime_sixtySevenBM_2499139 : Nat.Prime 2499139 := by norm_num
private theorem prime_sixtySevenBM_2578217 : Nat.Prime 2578217 := by norm_num
private theorem prime_sixtySevenBM_2826443 : Nat.Prime 2826443 := by norm_num
private theorem prime_sixtySevenBM_3225883 : Nat.Prime 3225883 := by norm_num
private theorem prime_sixtySevenBM_3347543 : Nat.Prime 3347543 := by norm_num
private theorem prime_sixtySevenBM_3413357 : Nat.Prime 3413357 := by norm_num
private theorem prime_sixtySevenBM_3619877 : Nat.Prime 3619877 := by norm_num
private theorem prime_sixtySevenBM_4043999 : Nat.Prime 4043999 := by norm_num
private theorem prime_sixtySevenBM_4330589 : Nat.Prime 4330589 := by norm_num
private theorem prime_sixtySevenBM_4949951 : Nat.Prime 4949951 := by norm_num
private theorem prime_sixtySevenBM_5093549 : Nat.Prime 5093549 := by norm_num
private theorem prime_sixtySevenBM_5679269 : Nat.Prime 5679269 := by norm_num
private theorem prime_sixtySevenBM_5888741 : Nat.Prime 5888741 := by norm_num
private theorem prime_sixtySevenBM_6422189 : Nat.Prime 6422189 := by norm_num
private theorem prime_sixtySevenBM_6680027 : Nat.Prime 6680027 := by norm_num
private theorem prime_sixtySevenBM_7157261 : Nat.Prime 7157261 := by norm_num
private theorem prime_sixtySevenBM_7660921 : Nat.Prime 7660921 := by norm_num
private theorem prime_sixtySevenBM_7977043 : Nat.Prime 7977043 := by norm_num
private theorem prime_sixtySevenBM_8750591 : Nat.Prime 8750591 := by norm_num
private theorem prime_sixtySevenBM_8832337 : Nat.Prime 8832337 := by norm_num
private theorem prime_sixtySevenBM_9487733 : Nat.Prime 9487733 := by norm_num
private theorem prime_sixtySevenBM_9527339 : Nat.Prime 9527339 := by norm_num
private theorem prime_sixtySevenBM_10515217 : Nat.Prime 10515217 := by norm_num
private theorem prime_sixtySevenBM_11198879 : Nat.Prime 11198879 := by norm_num
private theorem prime_sixtySevenBM_11588219 : Nat.Prime 11588219 := by norm_num
private theorem prime_sixtySevenBM_11703511 : Nat.Prime 11703511 := by norm_num
private theorem prime_sixtySevenBM_12351629 : Nat.Prime 12351629 := by norm_num
private theorem prime_sixtySevenBM_12514013 : Nat.Prime 12514013 := by norm_num
private theorem prime_sixtySevenBM_12605743 : Nat.Prime 12605743 := by norm_num
private theorem prime_sixtySevenBM_12918349 : Nat.Prime 12918349 := by norm_num
private theorem prime_sixtySevenBM_13489097 : Nat.Prime 13489097 := by norm_num
private theorem prime_sixtySevenBM_14808449 : Nat.Prime 14808449 := by norm_num
private theorem prime_sixtySevenBM_15110707 : Nat.Prime 15110707 := by norm_num
private theorem prime_sixtySevenBM_15883787 : Nat.Prime 15883787 := by norm_num
private theorem prime_sixtySevenBM_21202421 : Nat.Prime 21202421 := by norm_num
private theorem prime_sixtySevenBM_22066757 : Nat.Prime 22066757 := by norm_num
private theorem prime_sixtySevenBM_24621427 : Nat.Prime 24621427 := by norm_num
private theorem prime_sixtySevenBM_25144043 : Nat.Prime 25144043 := by norm_num
private theorem prime_sixtySevenBM_29524849 : Nat.Prime 29524849 := by norm_num
private theorem prime_sixtySevenBM_32266411 : Nat.Prime 32266411 := by
  apply lucas_primality 32266411 (2 : ZMod 32266411)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (97777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (97777, 1)] : List FactorBlock).map factorBlockValue).prod) = 32266411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_97777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32266411) ^ 16133205 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32266411) ^ 10755470 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32266411) ^ 6453282 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32266411) ^ 2933310 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 32266411) ^ 330 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_37474561 : Nat.Prime 37474561 := by
  apply lucas_primality 37474561 (7 : ZMod 37474561)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 37474561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 37474561) ^ 18737280 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 37474561) ^ 12491520 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 37474561) ^ 7494912 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 37474561) ^ 11520 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_39583751 : Nat.Prime 39583751 := by
  apply lucas_primality 39583751 (7 : ZMod 39583751)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (31667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (31667, 1)] : List FactorBlock).map factorBlockValue).prod) = 39583751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_31667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 39583751) ^ 19791875 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 39583751) ^ 7916750 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 39583751) ^ 1250 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_40170517 : Nat.Prime 40170517 := by
  apply lucas_primality 40170517 (2 : ZMod 40170517)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3347543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3347543, 1)] : List FactorBlock).map factorBlockValue).prod) = 40170517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_3347543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40170517) ^ 20085258 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40170517) ^ 13390172 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40170517) ^ 12 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_40519421 : Nat.Prime 40519421 := by
  apply lucas_primality 40519421 (2 : ZMod 40519421)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (601, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (601, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) = 40519421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_601
      · exact prime_sixtySevenBM_3371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40519421) ^ 20259710 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40519421) ^ 8103884 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40519421) ^ 67420 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 40519421) ^ 12020 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_46119959 : Nat.Prime 46119959 := by
  apply lucas_primality 46119959 (7 : ZMod 46119959)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (293, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (293, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 46119959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_211
      · exact prime_sixtySevenBM_293
      · exact prime_sixtySevenBM_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 46119959) ^ 23059979 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 46119959) ^ 218578 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 46119959) ^ 157406 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 46119959) ^ 123646 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_51195799 : Nat.Prime 51195799 := by
  apply lucas_primality 51195799 (7 : ZMod 51195799)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (69371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (69371, 1)] : List FactorBlock).map factorBlockValue).prod) = 51195799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_41
      · exact prime_sixtySevenBM_69371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 51195799) ^ 25597899 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 51195799) ^ 17065266 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 51195799) ^ 1248678 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 51195799) ^ 738 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_51673397 : Nat.Prime 51673397 := by
  apply lucas_primality 51673397 (2 : ZMod 51673397)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12918349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12918349, 1)] : List FactorBlock).map factorBlockValue).prod) = 51673397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_12918349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51673397) ^ 25836698 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 51673397) ^ 4 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_56506789 : Nat.Prime 56506789 := by
  apply lucas_primality 56506789 (2 : ZMod 56506789)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (167, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (167, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 56506789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_167
      · exact prime_sixtySevenBM_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56506789) ^ 28253394 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 56506789) ^ 18835596 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 56506789) ^ 4346676 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 56506789) ^ 338364 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 56506789) ^ 234468 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_65833927 : Nat.Prime 65833927 := by
  apply lucas_primality 65833927 (6 : ZMod 65833927)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (34613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (34613, 1)] : List FactorBlock).map factorBlockValue).prod) = 65833927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_317
      · exact prime_sixtySevenBM_34613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 65833927) ^ 32916963 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 65833927) ^ 21944642 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 65833927) ^ 207678 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 65833927) ^ 1902 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_68972269 : Nat.Prime 68972269 := by
  apply lucas_primality 68972269 (2 : ZMod 68972269)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (457, 1), (12577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (457, 1), (12577, 1)] : List FactorBlock).map factorBlockValue).prod) = 68972269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_457
      · exact prime_sixtySevenBM_12577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68972269) ^ 34486134 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 68972269) ^ 22990756 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 68972269) ^ 150924 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 68972269) ^ 5484 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_70761283 : Nat.Prime 70761283 := by
  apply lucas_primality 70761283 (2 : ZMod 70761283)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (20023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (20023, 1)] : List FactorBlock).map factorBlockValue).prod) = 70761283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_20023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70761283) ^ 35380641 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70761283) ^ 23587094 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70761283) ^ 3724278 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70761283) ^ 2282622 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70761283) ^ 3534 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_75211117 : Nat.Prime 75211117 := by
  apply lucas_primality 75211117 (2 : ZMod 75211117)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (937, 1), (6689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (937, 1), (6689, 1)] : List FactorBlock).map factorBlockValue).prod) = 75211117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_937
      · exact prime_sixtySevenBM_6689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75211117) ^ 37605558 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 75211117) ^ 25070372 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 75211117) ^ 80268 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 75211117) ^ 11244 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_89305519 : Nat.Prime 89305519 := by
  apply lucas_primality 89305519 (3 : ZMod 89305519)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (613, 1), (24281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (613, 1), (24281, 1)] : List FactorBlock).map factorBlockValue).prod) = 89305519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_613
      · exact prime_sixtySevenBM_24281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89305519) ^ 44652759 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 89305519) ^ 29768506 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 89305519) ^ 145686 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 89305519) ^ 3678 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_89670907 : Nat.Prime 89670907 := by
  apply lucas_primality 89670907 (2 : ZMod 89670907)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (37, 1), (10357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (37, 1), (10357, 1)] : List FactorBlock).map factorBlockValue).prod) = 89670907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_37
      · exact prime_sixtySevenBM_10357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89670907) ^ 44835453 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89670907) ^ 29890302 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89670907) ^ 6897762 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89670907) ^ 2423538 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89670907) ^ 8658 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_91962259 : Nat.Prime 91962259 := by
  apply lucas_primality 91962259 (2 : ZMod 91962259)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (251263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (251263, 1)] : List FactorBlock).map factorBlockValue).prod) = 91962259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_251263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91962259) ^ 45981129 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 91962259) ^ 30654086 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 91962259) ^ 1507578 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 91962259) ^ 366 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_102412171 : Nat.Prime 102412171 := by
  apply lucas_primality 102412171 (10 : ZMod 102412171)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (149, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (149, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) = 102412171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_149
      · exact prime_sixtySevenBM_1091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 102412171) ^ 51206085 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 102412171) ^ 34137390 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 102412171) ^ 20482434 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 102412171) ^ 14630310 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 102412171) ^ 687330 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 102412171) ^ 93870 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_118467593 : Nat.Prime 118467593 := by
  apply lucas_primality 118467593 (3 : ZMod 118467593)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14808449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14808449, 1)] : List FactorBlock).map factorBlockValue).prod) = 118467593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_14808449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 118467593) ^ 59233796 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 118467593) ^ 8 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_133398649 : Nat.Prime 133398649 := by
  apply lucas_primality 133398649 (7 : ZMod 133398649)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (461, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (461, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) = 133398649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_461
      · exact prime_sixtySevenBM_4019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133398649) ^ 66699324 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 133398649) ^ 44466216 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 133398649) ^ 289368 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 133398649) ^ 33192 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_137311519 : Nat.Prime 137311519 := by
  apply lucas_primality 137311519 (3 : ZMod 137311519)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (23, 1), (52369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (23, 1), (52369, 1)] : List FactorBlock).map factorBlockValue).prod) = 137311519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_52369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 137311519) ^ 68655759 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 137311519) ^ 45770506 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 137311519) ^ 7226922 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 137311519) ^ 5970066 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 137311519) ^ 2622 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_156645857 : Nat.Prime 156645857 := by
  apply lucas_primality 156645857 (3 : ZMod 156645857)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (571, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (571, 1), (8573, 1)] : List FactorBlock).map factorBlockValue).prod) = 156645857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_571
      · exact prime_sixtySevenBM_8573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 156645857) ^ 78322928 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 156645857) ^ 274336 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 156645857) ^ 18272 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_169311217 : Nat.Prime 169311217 := by
  apply lucas_primality 169311217 (5 : ZMod 169311217)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1567, 1), (2251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1567, 1), (2251, 1)] : List FactorBlock).map factorBlockValue).prod) = 169311217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1567
      · exact prime_sixtySevenBM_2251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 169311217) ^ 84655608 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 169311217) ^ 56437072 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 169311217) ^ 108048 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 169311217) ^ 75216 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_181736609 : Nat.Prime 181736609 := by
  apply lucas_primality 181736609 (3 : ZMod 181736609)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5679269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5679269, 1)] : List FactorBlock).map factorBlockValue).prod) = 181736609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5679269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 181736609) ^ 90868304 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 181736609) ^ 32 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_190367423 : Nat.Prime 190367423 := by
  apply lucas_primality 190367423 (7 : ZMod 190367423)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (839, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (839, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 190367423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_839
      · exact prime_sixtySevenBM_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 190367423) ^ 95183711 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 190367423) ^ 27195346 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 190367423) ^ 10019338 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 190367423) ^ 226898 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 190367423) ^ 223174 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_193092043 : Nat.Prime 193092043 := by
  apply lucas_primality 193092043 (2 : ZMod 193092043)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (13, 1), (41, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (13, 1), (41, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 193092043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_41
      · exact prime_sixtySevenBM_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 193092043) ^ 96546021 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 193092043) ^ 64364014 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 193092043) ^ 17553822 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 193092043) ^ 14853234 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 193092043) ^ 4709562 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 193092043) ^ 386958 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_207790753 : Nat.Prime 207790753 := by
  apply lucas_primality 207790753 (5 : ZMod 207790753)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (167, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (167, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) = 207790753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_167
      · exact prime_sixtySevenBM_997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 207790753) ^ 103895376 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 207790753) ^ 69263584 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 207790753) ^ 15983904 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 207790753) ^ 1244256 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 207790753) ^ 208416 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_269731939 : Nat.Prime 269731939 := by
  apply lucas_primality 269731939 (2 : ZMod 269731939)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (6422189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (6422189, 1)] : List FactorBlock).map factorBlockValue).prod) = 269731939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_6422189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 269731939) ^ 134865969 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 269731939) ^ 89910646 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 269731939) ^ 38533134 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 269731939) ^ 42 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_270368737 : Nat.Prime 270368737 := by
  apply lucas_primality 270368737 (5 : ZMod 270368737)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (256031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (256031, 1)] : List FactorBlock).map factorBlockValue).prod) = 270368737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_256031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 270368737) ^ 135184368 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 270368737) ^ 90122912 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 270368737) ^ 24578976 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 270368737) ^ 1056 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_279208129 : Nat.Prime 279208129 := by
  apply lucas_primality 279208129 (11 : ZMod 279208129)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (1454209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (1454209, 1)] : List FactorBlock).map factorBlockValue).prod) = 279208129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1454209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 279208129) ^ 139604064 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 279208129) ^ 93069376 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 279208129) ^ 192 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_287017811 : Nat.Prime 287017811 := by
  apply lucas_primality 287017811 (2 : ZMod 287017811)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (470521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (470521, 1)] : List FactorBlock).map factorBlockValue).prod) = 287017811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_470521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 287017811) ^ 143508905 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 287017811) ^ 57403562 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 287017811) ^ 4705210 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 287017811) ^ 610 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_329038277 : Nat.Prime 329038277 := by
  apply lucas_primality 329038277 (2 : ZMod 329038277)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (23, 1), (26891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (23, 1), (26891, 1)] : List FactorBlock).map factorBlockValue).prod) = 329038277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_26891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 329038277) ^ 164519138 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 329038277) ^ 47005468 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 329038277) ^ 17317804 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 329038277) ^ 14306012 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 329038277) ^ 12236 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_335385077 : Nat.Prime 335385077 := by
  apply lucas_primality 335385077 (2 : ZMod 335385077)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (61, 1), (105733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (61, 1), (105733, 1)] : List FactorBlock).map factorBlockValue).prod) = 335385077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_105733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 335385077) ^ 167692538 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 335385077) ^ 25798852 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 335385077) ^ 5498116 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 335385077) ^ 3172 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_360509381 : Nat.Prime 360509381 := by
  apply lucas_primality 360509381 (2 : ZMod 360509381)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (131, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (131, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) = 360509381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_131
      · exact prime_sixtySevenBM_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 360509381) ^ 180254690 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 360509381) ^ 72101876 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 360509381) ^ 51501340 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 360509381) ^ 32773580 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 360509381) ^ 2751980 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 360509381) ^ 201740 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_376007329 : Nat.Prime 376007329 := by
  apply lucas_primality 376007329 (14 : ZMod 376007329)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (1305581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (1305581, 1)] : List FactorBlock).map factorBlockValue).prod) = 376007329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1305581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 376007329) ^ 188003664 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (14 : ZMod 376007329) ^ 125335776 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (14 : ZMod 376007329) ^ 288 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_380110151 : Nat.Prime 380110151 := by
  apply lucas_primality 380110151 (7 : ZMod 380110151)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (47, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (47, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod) = 380110151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_47
      · exact prime_sixtySevenBM_3301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 380110151) ^ 190055075 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 380110151) ^ 76022030 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 380110151) ^ 54301450 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 380110151) ^ 8087450 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 380110151) ^ 115150 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_381311863 : Nat.Prime 381311863 := by
  apply lucas_primality 381311863 (5 : ZMod 381311863)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (1717621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (1717621, 1)] : List FactorBlock).map factorBlockValue).prod) = 381311863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_37
      · exact prime_sixtySevenBM_1717621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 381311863) ^ 190655931 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 381311863) ^ 127103954 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 381311863) ^ 10305726 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 381311863) ^ 222 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_443714743 : Nat.Prime 443714743 := by
  apply lucas_primality 443714743 (3 : ZMod 443714743)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1741, 1), (14159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1741, 1), (14159, 1)] : List FactorBlock).map factorBlockValue).prod) = 443714743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1741
      · exact prime_sixtySevenBM_14159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 443714743) ^ 221857371 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 443714743) ^ 147904914 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 443714743) ^ 254862 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 443714743) ^ 31338 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_446436769 : Nat.Prime 446436769 := by
  apply lucas_primality 446436769 (17 : ZMod 446436769)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (19, 1), (311, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (19, 1), (311, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod) = 446436769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_311
      · exact prime_sixtySevenBM_787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 446436769) ^ 223218384 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 446436769) ^ 148812256 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 446436769) ^ 23496672 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 446436769) ^ 1435488 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 446436769) ^ 567264 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_582229997 : Nat.Prime 582229997 := by
  apply lucas_primality 582229997 (2 : ZMod 582229997)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (7660921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (7660921, 1)] : List FactorBlock).map factorBlockValue).prod) = 582229997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_7660921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 582229997) ^ 291114998 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 582229997) ^ 30643684 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 582229997) ^ 76 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_596188609 : Nat.Prime 596188609 := by
  apply lucas_primality 596188609 (17 : ZMod 596188609)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (47, 1), (66067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (47, 1), (66067, 1)] : List FactorBlock).map factorBlockValue).prod) = 596188609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_47
      · exact prime_sixtySevenBM_66067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 596188609) ^ 298094304 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 596188609) ^ 198729536 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 596188609) ^ 12684864 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 596188609) ^ 9024 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_676783621 : Nat.Prime 676783621 := by
  apply lucas_primality 676783621 (6 : ZMod 676783621)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (337, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (337, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) = 676783621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_337
      · exact prime_sixtySevenBM_3719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 676783621) ^ 338391810 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 676783621) ^ 225594540 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 676783621) ^ 135356724 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 676783621) ^ 2008260 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 676783621) ^ 181980 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_722387957 : Nat.Prime 722387957 := by
  apply lucas_primality 722387957 (2 : ZMod 722387957)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (101, 1), (77743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (101, 1), (77743, 1)] : List FactorBlock).map factorBlockValue).prod) = 722387957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_101
      · exact prime_sixtySevenBM_77743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 722387957) ^ 361193978 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 722387957) ^ 31408172 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 722387957) ^ 7152356 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 722387957) ^ 9292 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_765950309 : Nat.Prime 765950309 := by
  apply lucas_primality 765950309 (2 : ZMod 765950309)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (821, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (821, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 765950309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_179
      · exact prime_sixtySevenBM_821
      · exact prime_sixtySevenBM_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 765950309) ^ 382975154 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 765950309) ^ 4279052 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 765950309) ^ 932948 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 765950309) ^ 587836 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_894134869 : Nat.Prime 894134869 := by
  apply lucas_primality 894134869 (2 : ZMod 894134869)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (257, 1), (26357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (257, 1), (26357, 1)] : List FactorBlock).map factorBlockValue).prod) = 894134869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_257
      · exact prime_sixtySevenBM_26357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 894134869) ^ 447067434 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 894134869) ^ 298044956 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 894134869) ^ 81284988 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 894134869) ^ 3479124 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 894134869) ^ 33924 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1152268921 : Nat.Prime 1152268921 := by
  apply lucas_primality 1152268921 (7 : ZMod 1152268921)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (41, 1), (47, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (41, 1), (47, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152268921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_41
      · exact prime_sixtySevenBM_47
      · exact prime_sixtySevenBM_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1152268921) ^ 576134460 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152268921) ^ 384089640 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152268921) ^ 230453784 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152268921) ^ 104751720 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152268921) ^ 28104120 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152268921) ^ 24516360 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1152268921) ^ 7630920 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1304920349 : Nat.Prime 1304920349 := by
  apply lucas_primality 1304920349 (2 : ZMod 1304920349)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1699, 1), (192013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1699, 1), (192013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1304920349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_1699
      · exact prime_sixtySevenBM_192013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1304920349) ^ 652460174 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1304920349) ^ 768052 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1304920349) ^ 6796 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1384024211 : Nat.Prime 1384024211 := by
  apply lucas_primality 1384024211 (2 : ZMod 1384024211)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (1370321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (1370321, 1)] : List FactorBlock).map factorBlockValue).prod) = 1384024211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_101
      · exact prime_sixtySevenBM_1370321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1384024211) ^ 692012105 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384024211) ^ 276804842 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384024211) ^ 13703210 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1384024211) ^ 1010 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1450627873 : Nat.Prime 1450627873 := by
  apply lucas_primality 1450627873 (5 : ZMod 1450627873)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (15110707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (15110707, 1)] : List FactorBlock).map factorBlockValue).prod) = 1450627873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_15110707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1450627873) ^ 725313936 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1450627873) ^ 483542624 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1450627873) ^ 96 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1811625971 : Nat.Prime 1811625971 := by
  apply lucas_primality 1811625971 (2 : ZMod 1811625971)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (2352761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (2352761, 1)] : List FactorBlock).map factorBlockValue).prod) = 1811625971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_2352761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1811625971) ^ 905812985 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1811625971) ^ 362325194 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1811625971) ^ 258803710 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1811625971) ^ 164693270 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1811625971) ^ 770 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1883613437 : Nat.Prime 1883613437 := by
  apply lucas_primality 1883613437 (2 : ZMod 1883613437)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251, 1), (1876109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251, 1), (1876109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1883613437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_251
      · exact prime_sixtySevenBM_1876109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1883613437) ^ 941806718 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1883613437) ^ 7504436 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1883613437) ^ 1004 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1898935523 : Nat.Prime 1898935523 := by
  apply lucas_primality 1898935523 (2 : ZMod 1898935523)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (23, 1), (311, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (23, 1), (311, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1898935523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_311
      · exact prime_sixtySevenBM_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1898935523) ^ 949467761 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898935523) ^ 172630502 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898935523) ^ 82562414 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898935523) ^ 6105902 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898935523) ^ 1731026 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2369351861 : Nat.Prime 2369351861 := by
  apply lucas_primality 2369351861 (2 : ZMod 2369351861)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (118467593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (118467593, 1)] : List FactorBlock).map factorBlockValue).prod) = 2369351861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_118467593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2369351861) ^ 1184675930 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2369351861) ^ 473870372 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2369351861) ^ 20 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2416656757 : Nat.Prime 2416656757 := by
  apply lucas_primality 2416656757 (2 : ZMod 2416656757)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (3413357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (3413357, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416656757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_59
      · exact prime_sixtySevenBM_3413357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2416656757) ^ 1208328378 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2416656757) ^ 805552252 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2416656757) ^ 40960284 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2416656757) ^ 708 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2446402771 : Nat.Prime 2446402771 := by
  apply lucas_primality 2446402771 (2 : ZMod 2446402771)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (1294393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (1294393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2446402771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_1294393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2446402771) ^ 1223201385 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2446402771) ^ 815467590 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2446402771) ^ 489280554 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2446402771) ^ 349486110 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2446402771) ^ 1890 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2511861967 : Nat.Prime 2511861967 := by
  apply lucas_primality 2511861967 (3 : ZMod 2511861967)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (53, 1), (149, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (53, 1), (149, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 2511861967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_41
      · exact prime_sixtySevenBM_53
      · exact prime_sixtySevenBM_149
      · exact prime_sixtySevenBM_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2511861967) ^ 1255930983 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2511861967) ^ 837287322 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2511861967) ^ 61264926 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2511861967) ^ 47393622 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2511861967) ^ 16858134 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2511861967) ^ 5827986 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2532053443 : Nat.Prime 2532053443 := by
  apply lucas_primality 2532053443 (2 : ZMod 2532053443)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (911, 1), (463237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (911, 1), (463237, 1)] : List FactorBlock).map factorBlockValue).prod) = 2532053443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_911
      · exact prime_sixtySevenBM_463237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2532053443) ^ 1266026721 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532053443) ^ 844017814 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532053443) ^ 2779422 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532053443) ^ 5466 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3791699759 : Nat.Prime 3791699759 := by
  apply lucas_primality 3791699759 (7 : ZMod 3791699759)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (24621427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (24621427, 1)] : List FactorBlock).map factorBlockValue).prod) = 3791699759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_24621427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3791699759) ^ 1895849879 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3791699759) ^ 541671394 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3791699759) ^ 344699978 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3791699759) ^ 154 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4334327743 : Nat.Prime 4334327743 := by
  apply lucas_primality 4334327743 (5 : ZMod 4334327743)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (722387957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (722387957, 1)] : List FactorBlock).map factorBlockValue).prod) = 4334327743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_722387957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4334327743) ^ 2167163871 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4334327743) ^ 1444775914 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4334327743) ^ 6 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4437147431 : Nat.Prime 4437147431 := by
  apply lucas_primality 4437147431 (13 : ZMod 4437147431)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (443714743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (443714743, 1)] : List FactorBlock).map factorBlockValue).prod) = 4437147431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_443714743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 4437147431) ^ 2218573715 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4437147431) ^ 887429486 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4437147431) ^ 10 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4689508379 : Nat.Prime 4689508379 := by
  apply lucas_primality 4689508379 (2 : ZMod 4689508379)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (47, 1), (881, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (47, 1), (881, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) = 4689508379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_47
      · exact prime_sixtySevenBM_881
      · exact prime_sixtySevenBM_3331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4689508379) ^ 2344754189 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4689508379) ^ 275853434 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4689508379) ^ 99776774 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4689508379) ^ 5322938 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4689508379) ^ 1407838 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4854459817 : Nat.Prime 4854459817 := by
  apply lucas_primality 4854459817 (5 : ZMod 4854459817)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (197, 1), (114083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (197, 1), (114083, 1)] : List FactorBlock).map factorBlockValue).prod) = 4854459817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_197
      · exact prime_sixtySevenBM_114083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4854459817) ^ 2427229908 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4854459817) ^ 1618153272 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4854459817) ^ 24641928 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4854459817) ^ 42552 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4964949053 : Nat.Prime 4964949053 := by
  apply lucas_primality 4964949053 (2 : ZMod 4964949053)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (53, 1), (176087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (53, 1), (176087, 1)] : List FactorBlock).map factorBlockValue).prod) = 4964949053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_53
      · exact prime_sixtySevenBM_176087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4964949053) ^ 2482474526 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4964949053) ^ 709278436 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4964949053) ^ 261313108 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4964949053) ^ 93678284 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4964949053) ^ 28196 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_5091715633 : Nat.Prime 5091715633 := by
  apply lucas_primality 5091715633 (5 : ZMod 5091715633)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (89, 1), (32213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (89, 1), (32213, 1)] : List FactorBlock).map factorBlockValue).prod) = 5091715633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_37
      · exact prime_sixtySevenBM_89
      · exact prime_sixtySevenBM_32213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5091715633) ^ 2545857816 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5091715633) ^ 1697238544 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5091715633) ^ 137613936 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5091715633) ^ 57210288 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5091715633) ^ 158064 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_5223159479 : Nat.Prime 5223159479 := by
  apply lucas_primality 5223159479 (13 : ZMod 5223159479)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (1289, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (1289, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) = 5223159479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_331
      · exact prime_sixtySevenBM_1289
      · exact prime_sixtySevenBM_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 5223159479) ^ 2611579739 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 5223159479) ^ 15779938 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 5223159479) ^ 4052102 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 5223159479) ^ 853318 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_6205830373 : Nat.Prime 6205830373 := by
  apply lucas_primality 6205830373 (6 : ZMod 6205830373)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (467, 1), (52733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (467, 1), (52733, 1)] : List FactorBlock).map factorBlockValue).prod) = 6205830373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_467
      · exact prime_sixtySevenBM_52733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6205830373) ^ 3102915186 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6205830373) ^ 2068610124 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6205830373) ^ 886547196 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6205830373) ^ 13288716 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6205830373) ^ 117684 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_6578042453 : Nat.Prime 6578042453 := by
  apply lucas_primality 6578042453 (2 : ZMod 6578042453)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1181, 1), (1392473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1181, 1), (1392473, 1)] : List FactorBlock).map factorBlockValue).prod) = 6578042453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_1181
      · exact prime_sixtySevenBM_1392473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6578042453) ^ 3289021226 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6578042453) ^ 5569892 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6578042453) ^ 4724 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_7583399519 : Nat.Prime 7583399519 := by
  apply lucas_primality 7583399519 (11 : ZMod 7583399519)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3791699759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3791699759, 1)] : List FactorBlock).map factorBlockValue).prod) = 7583399519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3791699759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 7583399519) ^ 3791699759 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 7583399519) ^ 2 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_7869657811 : Nat.Prime 7869657811 := by
  apply lucas_primality 7869657811 (2 : ZMod 7869657811)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (37474561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (37474561, 1)] : List FactorBlock).map factorBlockValue).prod) = 7869657811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_37474561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7869657811) ^ 3934828905 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7869657811) ^ 2623219270 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7869657811) ^ 1573931562 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7869657811) ^ 1124236830 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7869657811) ^ 210 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_7949800351 : Nat.Prime 7949800351 := by
  apply lucas_primality 7949800351 (6 : ZMod 7949800351)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (5888741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (5888741, 1)] : List FactorBlock).map factorBlockValue).prod) = 7949800351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_5888741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 7949800351) ^ 3974900175 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 7949800351) ^ 2649933450 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 7949800351) ^ 1589960070 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 7949800351) ^ 1350 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_9531373177 : Nat.Prime 9531373177 := by
  apply lucas_primality 9531373177 (5 : ZMod 9531373177)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (947, 1), (10753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (947, 1), (10753, 1)] : List FactorBlock).map factorBlockValue).prod) = 9531373177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_947
      · exact prime_sixtySevenBM_10753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9531373177) ^ 4765686588 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9531373177) ^ 3177124392 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9531373177) ^ 733182552 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9531373177) ^ 10064808 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9531373177) ^ 886392 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_10147600493 : Nat.Prime 10147600493 := by
  apply lucas_primality 10147600493 (2 : ZMod 10147600493)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (101, 1), (1477519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (101, 1), (1477519, 1)] : List FactorBlock).map factorBlockValue).prod) = 10147600493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_101
      · exact prime_sixtySevenBM_1477519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10147600493) ^ 5073800246 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10147600493) ^ 596917676 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10147600493) ^ 100471292 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10147600493) ^ 6868 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_10262851793 : Nat.Prime 10262851793 := by
  apply lucas_primality 10262851793 (3 : ZMod 10262851793)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (61, 1), (10515217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (61, 1), (10515217, 1)] : List FactorBlock).map factorBlockValue).prod) = 10262851793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_10515217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10262851793) ^ 5131425896 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10262851793) ^ 168243472 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10262851793) ^ 976 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_10334947817 : Nat.Prime 10334947817 := by
  apply lucas_primality 10334947817 (3 : ZMod 10334947817)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (769, 1), (16633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (769, 1), (16633, 1)] : List FactorBlock).map factorBlockValue).prod) = 10334947817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_101
      · exact prime_sixtySevenBM_769
      · exact prime_sixtySevenBM_16633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10334947817) ^ 5167473908 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10334947817) ^ 102326216 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10334947817) ^ 13439464 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10334947817) ^ 621352 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_10706497969 : Nat.Prime 10706497969 := by
  apply lucas_primality 10706497969 (13 : ZMod 10706497969)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (109, 1), (2046349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (109, 1), (2046349, 1)] : List FactorBlock).map factorBlockValue).prod) = 10706497969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_109
      · exact prime_sixtySevenBM_2046349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 10706497969) ^ 5353248984 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 10706497969) ^ 3568832656 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 10706497969) ^ 98224752 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 10706497969) ^ 5232 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_10858179781 : Nat.Prime 10858179781 := by
  apply lucas_primality 10858179781 (2 : ZMod 10858179781)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (89, 1), (96827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (89, 1), (96827, 1)] : List FactorBlock).map factorBlockValue).prod) = 10858179781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_89
      · exact prime_sixtySevenBM_96827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10858179781) ^ 5429089890 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10858179781) ^ 3619393260 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10858179781) ^ 2171635956 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10858179781) ^ 1551168540 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10858179781) ^ 122002020 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10858179781) ^ 112140 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_12316990417 : Nat.Prime 12316990417 := by
  apply lucas_primality 12316990417 (10 : ZMod 12316990417)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 2), (887903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 2), (887903, 1)] : List FactorBlock).map factorBlockValue).prod) = 12316990417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_887903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 12316990417) ^ 6158495208 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 12316990417) ^ 4105663472 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 12316990417) ^ 724528848 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 12316990417) ^ 13872 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_12440913479 : Nat.Prime 12440913479 := by
  apply lucas_primality 12440913479 (7 : ZMod 12440913479)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (27067, 1), (32831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (27067, 1), (32831, 1)] : List FactorBlock).map factorBlockValue).prod) = 12440913479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_27067
      · exact prime_sixtySevenBM_32831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 12440913479) ^ 6220456739 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 12440913479) ^ 1777273354 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 12440913479) ^ 459634 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 12440913479) ^ 378938 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_14320495697 : Nat.Prime 14320495697 := by
  apply lucas_primality 14320495697 (3 : ZMod 14320495697)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (53, 1), (1299029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (53, 1), (1299029, 1)] : List FactorBlock).map factorBlockValue).prod) = 14320495697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_53
      · exact prime_sixtySevenBM_1299029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14320495697) ^ 7160247848 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14320495697) ^ 1101576592 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14320495697) ^ 270198032 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14320495697) ^ 11024 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_15870697691 : Nat.Prime 15870697691 := by
  apply lucas_primality 15870697691 (2 : ZMod 15870697691)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (51195799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (51195799, 1)] : List FactorBlock).map factorBlockValue).prod) = 15870697691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_51195799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15870697691) ^ 7935348845 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15870697691) ^ 3174139538 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15870697691) ^ 511957990 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15870697691) ^ 310 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_22534773017 : Nat.Prime 22534773017 := by
  apply lucas_primality 22534773017 (3 : ZMod 22534773017)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (379, 1), (1061759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (379, 1), (1061759, 1)] : List FactorBlock).map factorBlockValue).prod) = 22534773017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_379
      · exact prime_sixtySevenBM_1061759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22534773017) ^ 11267386508 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 22534773017) ^ 3219253288 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 22534773017) ^ 59458504 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 22534773017) ^ 21224 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_25087269967 : Nat.Prime 25087269967 := by
  apply lucas_primality 25087269967 (3 : ZMod 25087269967)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (380110151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (380110151, 1)] : List FactorBlock).map factorBlockValue).prod) = 25087269967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_380110151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25087269967) ^ 12543634983 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 25087269967) ^ 8362423322 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 25087269967) ^ 2280660906 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 25087269967) ^ 66 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_25667997599 : Nat.Prime 25667997599 := by
  apply lucas_primality 25667997599 (17 : ZMod 25667997599)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (641, 1), (13339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (641, 1), (13339, 1)] : List FactorBlock).map factorBlockValue).prod) = 25667997599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_79
      · exact prime_sixtySevenBM_641
      · exact prime_sixtySevenBM_13339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 25667997599) ^ 12833998799 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 25667997599) ^ 1350947242 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 25667997599) ^ 324911362 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 25667997599) ^ 40043678 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 25667997599) ^ 1924282 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_26189728399 : Nat.Prime 26189728399 := by
  apply lucas_primality 26189728399 (3 : ZMod 26189728399)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (907, 1), (997, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (907, 1), (997, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 26189728399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_907
      · exact prime_sixtySevenBM_997
      · exact prime_sixtySevenBM_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26189728399) ^ 13094864199 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26189728399) ^ 8729909466 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26189728399) ^ 28875114 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26189728399) ^ 26268534 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26189728399) ^ 16277022 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_26629795691 : Nat.Prime 26629795691 := by
  apply lucas_primality 26629795691 (2 : ZMod 26629795691)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (156645857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (156645857, 1)] : List FactorBlock).map factorBlockValue).prod) = 26629795691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_156645857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26629795691) ^ 13314897845 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 26629795691) ^ 5325959138 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 26629795691) ^ 1566458570 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 26629795691) ^ 170 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_28693585387 : Nat.Prime 28693585387 := by
  apply lucas_primality 28693585387 (2 : ZMod 28693585387)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (2213, 1), (17569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (2213, 1), (17569, 1)] : List FactorBlock).map factorBlockValue).prod) = 28693585387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_41
      · exact prime_sixtySevenBM_2213
      · exact prime_sixtySevenBM_17569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28693585387) ^ 14346792693 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28693585387) ^ 9564528462 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28693585387) ^ 699843546 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28693585387) ^ 12965922 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28693585387) ^ 1633194 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_29353627409 : Nat.Prime 29353627409 := by
  apply lucas_primality 29353627409 (3 : ZMod 29353627409)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (47, 1), (167, 1), (33391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (47, 1), (167, 1), (33391, 1)] : List FactorBlock).map factorBlockValue).prod) = 29353627409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_47
      · exact prime_sixtySevenBM_167
      · exact prime_sixtySevenBM_33391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29353627409) ^ 14676813704 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29353627409) ^ 4193375344 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29353627409) ^ 624545264 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29353627409) ^ 175770224 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 29353627409) ^ 879088 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_30550293799 : Nat.Prime 30550293799 := by
  apply lucas_primality 30550293799 (3 : ZMod 30550293799)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5091715633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5091715633, 1)] : List FactorBlock).map factorBlockValue).prod) = 30550293799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5091715633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30550293799) ^ 15275146899 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30550293799) ^ 10183431266 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30550293799) ^ 6 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_30824662541 : Nat.Prime 30824662541 := by
  apply lucas_primality 30824662541 (2 : ZMod 30824662541)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (11588219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (11588219, 1)] : List FactorBlock).map factorBlockValue).prod) = 30824662541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_11588219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30824662541) ^ 15412331270 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30824662541) ^ 6164932508 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30824662541) ^ 4403523220 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30824662541) ^ 1622350660 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30824662541) ^ 2660 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_35699727223 : Nat.Prime 35699727223 := by
  apply lucas_primality 35699727223 (5 : ZMod 35699727223)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 2), (60539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 2), (60539, 1)] : List FactorBlock).map factorBlockValue).prod) = 35699727223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_181
      · exact prime_sixtySevenBM_60539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35699727223) ^ 17849863611 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 35699727223) ^ 11899909074 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 35699727223) ^ 197236062 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 35699727223) ^ 589698 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_38958963943 : Nat.Prime 38958963943 := by
  apply lucas_primality 38958963943 (3 : ZMod 38958963943)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (941, 1), (97187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (941, 1), (97187, 1)] : List FactorBlock).map factorBlockValue).prod) = 38958963943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_71
      · exact prime_sixtySevenBM_941
      · exact prime_sixtySevenBM_97187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38958963943) ^ 19479481971 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 38958963943) ^ 12986321314 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 38958963943) ^ 548717802 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 38958963943) ^ 41401662 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 38958963943) ^ 400866 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_42569981527 : Nat.Prime 42569981527 := by
  apply lucas_primality 42569981527 (3 : ZMod 42569981527)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (149, 1), (2070323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (149, 1), (2070323, 1)] : List FactorBlock).map factorBlockValue).prod) = 42569981527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_149
      · exact prime_sixtySevenBM_2070323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42569981527) ^ 21284990763 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 42569981527) ^ 14189993842 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 42569981527) ^ 1850868762 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 42569981527) ^ 285704574 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 42569981527) ^ 20562 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_44926547579 : Nat.Prime 44926547579 := by
  apply lucas_primality 44926547579 (2 : ZMod 44926547579)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (157, 1), (653, 1), (19919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (157, 1), (653, 1), (19919, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926547579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_157
      · exact prime_sixtySevenBM_653
      · exact prime_sixtySevenBM_19919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44926547579) ^ 22463273789 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926547579) ^ 4084231598 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926547579) ^ 286156354 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926547579) ^ 68800226 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926547579) ^ 2255462 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_49267961669 : Nat.Prime 49267961669 := by
  apply lucas_primality 49267961669 (2 : ZMod 49267961669)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12316990417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12316990417, 1)] : List FactorBlock).map factorBlockValue).prod) = 49267961669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_12316990417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 49267961669) ^ 24633980834 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 49267961669) ^ 4 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_56960482199 : Nat.Prime 56960482199 := by
  apply lucas_primality 56960482199 (11 : ZMod 56960482199)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (360509381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (360509381, 1)] : List FactorBlock).map factorBlockValue).prod) = 56960482199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_79
      · exact prime_sixtySevenBM_360509381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 56960482199) ^ 28480241099 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 56960482199) ^ 721018762 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 56960482199) ^ 158 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_60264137621 : Nat.Prime 60264137621 := by
  apply lucas_primality 60264137621 (2 : ZMod 60264137621)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (421, 1), (7157261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (421, 1), (7157261, 1)] : List FactorBlock).map factorBlockValue).prod) = 60264137621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_421
      · exact prime_sixtySevenBM_7157261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60264137621) ^ 30132068810 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 60264137621) ^ 12052827524 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 60264137621) ^ 143145220 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 60264137621) ^ 8420 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_62580510101 : Nat.Prime 62580510101 := by
  apply lucas_primality 62580510101 (2 : ZMod 62580510101)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (43, 1), (2011, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (43, 1), (2011, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 62580510101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_43
      · exact prime_sixtySevenBM_2011
      · exact prime_sixtySevenBM_7237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62580510101) ^ 31290255050 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 62580510101) ^ 12516102020 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 62580510101) ^ 1455360700 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 62580510101) ^ 31119100 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 62580510101) ^ 8647300 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_69349243889 : Nat.Prime 69349243889 := by
  apply lucas_primality 69349243889 (3 : ZMod 69349243889)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4334327743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4334327743, 1)] : List FactorBlock).map factorBlockValue).prod) = 69349243889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_4334327743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 69349243889) ^ 34674621944 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69349243889) ^ 16 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_85884592267 : Nat.Prime 85884592267 := by
  apply lucas_primality 85884592267 (2 : ZMod 85884592267)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1753, 1), (247439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1753, 1), (247439, 1)] : List FactorBlock).map factorBlockValue).prod) = 85884592267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_1753
      · exact prime_sixtySevenBM_247439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85884592267) ^ 42942296133 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 85884592267) ^ 28628197422 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 85884592267) ^ 7807690206 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 85884592267) ^ 48992922 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 85884592267) ^ 347094 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_104166820049 : Nat.Prime 104166820049 := by
  apply lucas_primality 104166820049 (3 : ZMod 104166820049)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (29, 1), (197, 1), (49547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (29, 1), (197, 1), (49547, 1)] : List FactorBlock).map factorBlockValue).prod) = 104166820049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_29
      · exact prime_sixtySevenBM_197
      · exact prime_sixtySevenBM_49547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104166820049) ^ 52083410024 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 104166820049) ^ 4528992176 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 104166820049) ^ 3591959312 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 104166820049) ^ 528765584 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 104166820049) ^ 2102384 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_151160796119 : Nat.Prime 151160796119 := by
  apply lucas_primality 151160796119 (7 : ZMod 151160796119)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (739, 1), (1676621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (739, 1), (1676621, 1)] : List FactorBlock).map factorBlockValue).prod) = 151160796119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_739
      · exact prime_sixtySevenBM_1676621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 151160796119) ^ 75580398059 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 151160796119) ^ 2478045838 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 151160796119) ^ 204547762 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 151160796119) ^ 90158 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_153545451497 : Nat.Prime 153545451497 := by
  apply lucas_primality 153545451497 (3 : ZMod 153545451497)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (241, 1), (881, 1), (90397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (241, 1), (881, 1), (90397, 1)] : List FactorBlock).map factorBlockValue).prod) = 153545451497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_241
      · exact prime_sixtySevenBM_881
      · exact prime_sixtySevenBM_90397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 153545451497) ^ 76772725748 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 153545451497) ^ 637118056 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 153545451497) ^ 174285416 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 153545451497) ^ 1698568 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_163253882521 : Nat.Prime 163253882521 := by
  apply lucas_primality 163253882521 (23 : ZMod 163253882521)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (17, 1), (233, 1), (114487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (17, 1), (233, 1), (114487, 1)] : List FactorBlock).map factorBlockValue).prod) = 163253882521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_233
      · exact prime_sixtySevenBM_114487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 163253882521) ^ 81626941260 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (23 : ZMod 163253882521) ^ 54417960840 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (23 : ZMod 163253882521) ^ 32650776504 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (23 : ZMod 163253882521) ^ 9603169560 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (23 : ZMod 163253882521) ^ 700660440 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (23 : ZMod 163253882521) ^ 1425960 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_166065965591 : Nat.Prime 166065965591 := by
  apply lucas_primality 166065965591 (11 : ZMod 166065965591)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (107, 1), (401, 1), (55291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (107, 1), (401, 1), (55291, 1)] : List FactorBlock).map factorBlockValue).prod) = 166065965591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_107
      · exact prime_sixtySevenBM_401
      · exact prime_sixtySevenBM_55291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 166065965591) ^ 83032982795 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 166065965591) ^ 33213193118 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 166065965591) ^ 23723709370 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 166065965591) ^ 1552018370 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 166065965591) ^ 414129590 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 166065965591) ^ 3003490 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_176140999513 : Nat.Prime 176140999513 := by
  apply lucas_primality 176140999513 (5 : ZMod 176140999513)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2446402771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2446402771, 1)] : List FactorBlock).map factorBlockValue).prod) = 176140999513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_2446402771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 176140999513) ^ 88070499756 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 176140999513) ^ 58713666504 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 176140999513) ^ 72 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_182688848861 : Nat.Prime 182688848861 := by
  apply lucas_primality 182688848861 (2 : ZMod 182688848861)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1304920349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1304920349, 1)] : List FactorBlock).map factorBlockValue).prod) = 182688848861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_1304920349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 182688848861) ^ 91344424430 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 182688848861) ^ 36537769772 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 182688848861) ^ 26098406980 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 182688848861) ^ 140 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_187384811561 : Nat.Prime 187384811561 := by
  apply lucas_primality 187384811561 (7 : ZMod 187384811561)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (79, 1), (2578217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (79, 1), (2578217, 1)] : List FactorBlock).map factorBlockValue).prod) = 187384811561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_79
      · exact prime_sixtySevenBM_2578217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 187384811561) ^ 93692405780 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 187384811561) ^ 37476962312 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 187384811561) ^ 8147165720 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 187384811561) ^ 2371959640 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 187384811561) ^ 72680 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_205257035861 : Nat.Prime 205257035861 := by
  apply lucas_primality 205257035861 (2 : ZMod 205257035861)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (10262851793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (10262851793, 1)] : List FactorBlock).map factorBlockValue).prod) = 205257035861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_10262851793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 205257035861) ^ 102628517930 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 205257035861) ^ 41051407172 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 205257035861) ^ 20 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_208868370229 : Nat.Prime 208868370229 := by
  apply lucas_primality 208868370229 (2 : ZMod 208868370229)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (137, 1), (431, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (137, 1), (431, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) = 208868370229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_137
      · exact prime_sixtySevenBM_431
      · exact prime_sixtySevenBM_4679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 208868370229) ^ 104434185114 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 208868370229) ^ 69622790076 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 208868370229) ^ 29838338604 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 208868370229) ^ 1524586644 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 208868370229) ^ 484613388 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 208868370229) ^ 44639532 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_282907103119 : Nat.Prime 282907103119 := by
  apply lucas_primality 282907103119 (3 : ZMod 282907103119)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1597, 1), (29524849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1597, 1), (29524849, 1)] : List FactorBlock).map factorBlockValue).prod) = 282907103119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1597
      · exact prime_sixtySevenBM_29524849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 282907103119) ^ 141453551559 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 282907103119) ^ 94302367706 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 282907103119) ^ 177149094 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 282907103119) ^ 9582 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_304428014791 : Nat.Prime 304428014791 := by
  apply lucas_primality 304428014791 (6 : ZMod 304428014791)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (10147600493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (10147600493, 1)] : List FactorBlock).map factorBlockValue).prod) = 304428014791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_10147600493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 304428014791) ^ 152214007395 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 304428014791) ^ 101476004930 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 304428014791) ^ 60885602958 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 304428014791) ^ 30 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_333891614743 : Nat.Prime 333891614743 := by
  apply lucas_primality 333891614743 (19 : ZMod 333891614743)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (7949800351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (7949800351, 1)] : List FactorBlock).map factorBlockValue).prod) = 333891614743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_7949800351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 333891614743) ^ 166945807371 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 333891614743) ^ 111297204914 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 333891614743) ^ 47698802106 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 333891614743) ^ 42 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_362939851361 : Nat.Prime 362939851361 := by
  apply lucas_primality 362939851361 (3 : ZMod 362939851361)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (19, 1), (2053, 1), (58153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (19, 1), (2053, 1), (58153, 1)] : List FactorBlock).map factorBlockValue).prod) = 362939851361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_2053
      · exact prime_sixtySevenBM_58153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 362939851361) ^ 181469925680 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 362939851361) ^ 72587970272 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 362939851361) ^ 19102097440 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 362939851361) ^ 176785120 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 362939851361) ^ 6241120 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_387382846693 : Nat.Prime 387382846693 := by
  apply lucas_primality 387382846693 (5 : ZMod 387382846693)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (1898935523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (1898935523, 1)] : List FactorBlock).map factorBlockValue).prod) = 387382846693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_1898935523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 387382846693) ^ 193691423346 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 387382846693) ^ 129127615564 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 387382846693) ^ 22787226276 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 387382846693) ^ 204 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_444205651507 : Nat.Prime 444205651507 := by
  apply lucas_primality 444205651507 (2 : ZMod 444205651507)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (829, 1), (89305519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (829, 1), (89305519, 1)] : List FactorBlock).map factorBlockValue).prod) = 444205651507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_829
      · exact prime_sixtySevenBM_89305519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 444205651507) ^ 222102825753 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 444205651507) ^ 148068550502 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 444205651507) ^ 535833114 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 444205651507) ^ 4974 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_479014293097 : Nat.Prime 479014293097 := by
  apply lucas_primality 479014293097 (11 : ZMod 479014293097)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (761, 1), (460127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (761, 1), (460127, 1)] : List FactorBlock).map factorBlockValue).prod) = 479014293097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_761
      · exact prime_sixtySevenBM_460127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 479014293097) ^ 239507146548 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 479014293097) ^ 159671431032 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 479014293097) ^ 25211278584 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 479014293097) ^ 629453736 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 479014293097) ^ 1041048 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_479278999597 : Nat.Prime 479278999597 := by
  apply lucas_primality 479278999597 (2 : ZMod 479278999597)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (48787, 1), (818659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (48787, 1), (818659, 1)] : List FactorBlock).map factorBlockValue).prod) = 479278999597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_48787
      · exact prime_sixtySevenBM_818659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 479278999597) ^ 239639499798 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 479278999597) ^ 159759666532 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 479278999597) ^ 9823908 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 479278999597) ^ 585444 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_515307553603 : Nat.Prime 515307553603 := by
  apply lucas_primality 515307553603 (2 : ZMod 515307553603)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (85884592267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (85884592267, 1)] : List FactorBlock).map factorBlockValue).prod) = 515307553603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_85884592267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 515307553603) ^ 257653776801 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 515307553603) ^ 171769184534 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 515307553603) ^ 6 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_522467289137 : Nat.Prime 522467289137 := by
  apply lucas_primality 522467289137 (3 : ZMod 522467289137)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (2511861967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (2511861967, 1)] : List FactorBlock).map factorBlockValue).prod) = 522467289137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_2511861967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 522467289137) ^ 261233644568 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 522467289137) ^ 40189791472 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 522467289137) ^ 208 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_534659060591 : Nat.Prime 534659060591 := by
  apply lucas_primality 534659060591 (13 : ZMod 534659060591)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (676783621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (676783621, 1)] : List FactorBlock).map factorBlockValue).prod) = 534659060591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_79
      · exact prime_sixtySevenBM_676783621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 534659060591) ^ 267329530295 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 534659060591) ^ 106931812118 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 534659060591) ^ 6767836210 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 534659060591) ^ 790 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_571882390621 : Nat.Prime 571882390621 := by
  apply lucas_primality 571882390621 (7 : ZMod 571882390621)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (9531373177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (9531373177, 1)] : List FactorBlock).map factorBlockValue).prod) = 571882390621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_9531373177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 571882390621) ^ 285941195310 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 571882390621) ^ 190627463540 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 571882390621) ^ 114376478124 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 571882390621) ^ 60 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_616204461781 : Nat.Prime 616204461781 := by
  apply lucas_primality 616204461781 (6 : ZMod 616204461781)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (59, 2), (983441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (59, 2), (983441, 1)] : List FactorBlock).map factorBlockValue).prod) = 616204461781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_59
      · exact prime_sixtySevenBM_983441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 616204461781) ^ 308102230890 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 616204461781) ^ 205401487260 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 616204461781) ^ 123240892356 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 616204461781) ^ 10444143420 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 616204461781) ^ 626580 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_755227427057 : Nat.Prime 755227427057 := by
  apply lucas_primality 755227427057 (3 : ZMod 755227427057)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (1613, 1), (1721371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (1613, 1), (1721371, 1)] : List FactorBlock).map factorBlockValue).prod) = 755227427057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_1613
      · exact prime_sixtySevenBM_1721371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 755227427057) ^ 377613713528 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 755227427057) ^ 44425142768 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 755227427057) ^ 468212912 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 755227427057) ^ 438736 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_841123124801 : Nat.Prime 841123124801 := by
  apply lucas_primality 841123124801 (3 : ZMod 841123124801)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (7, 1), (809, 1), (92831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (7, 1), (809, 1), (92831, 1)] : List FactorBlock).map factorBlockValue).prod) = 841123124801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_809
      · exact prime_sixtySevenBM_92831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 841123124801) ^ 420561562400 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 841123124801) ^ 168224624960 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 841123124801) ^ 120160446400 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 841123124801) ^ 1039707200 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 841123124801) ^ 9060800 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_921638191597 : Nat.Prime 921638191597 := by
  apply lucas_primality 921638191597 (2 : ZMod 921638191597)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (335385077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (335385077, 1)] : List FactorBlock).map factorBlockValue).prod) = 921638191597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_229
      · exact prime_sixtySevenBM_335385077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 921638191597) ^ 460819095798 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 921638191597) ^ 307212730532 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 921638191597) ^ 4024620924 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 921638191597) ^ 2748 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_970889414447 : Nat.Prime 970889414447 := by
  apply lucas_primality 970889414447 (5 : ZMod 970889414447)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (69349243889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (69349243889, 1)] : List FactorBlock).map factorBlockValue).prod) = 970889414447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_69349243889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 970889414447) ^ 485444707223 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 970889414447) ^ 138698487778 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 970889414447) ^ 14 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1119238833199 : Nat.Prime 1119238833199 := by
  apply lucas_primality 1119238833199 (3 : ZMod 1119238833199)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (92357, 1), (2019769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (92357, 1), (2019769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1119238833199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_92357
      · exact prime_sixtySevenBM_2019769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1119238833199) ^ 559619416599 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1119238833199) ^ 373079611066 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1119238833199) ^ 12118614 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1119238833199) ^ 554142 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1141907537291 : Nat.Prime 1141907537291 := by
  apply lucas_primality 1141907537291 (6 : ZMod 1141907537291)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (54647, 1), (160739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (54647, 1), (160739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141907537291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_54647
      · exact prime_sixtySevenBM_160739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1141907537291) ^ 570953768645 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1141907537291) ^ 228381507458 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1141907537291) ^ 87839041330 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1141907537291) ^ 20896070 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1141907537291) ^ 7104110 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1273427027207 : Nat.Prime 1273427027207 := by
  apply lucas_primality 1273427027207 (5 : ZMod 1273427027207)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4637, 1), (137311519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4637, 1), (137311519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1273427027207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_4637
      · exact prime_sixtySevenBM_137311519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1273427027207) ^ 636713513603 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273427027207) ^ 274623038 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273427027207) ^ 9274 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1639138704013 : Nat.Prime 1639138704013 := by
  apply lucas_primality 1639138704013 (5 : ZMod 1639138704013)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4799, 1), (9487733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4799, 1), (9487733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1639138704013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_4799
      · exact prime_sixtySevenBM_9487733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1639138704013) ^ 819569352006 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1639138704013) ^ 546379568004 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1639138704013) ^ 341558388 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1639138704013) ^ 172764 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1935423941879 : Nat.Prime 1935423941879 := by
  apply lucas_primality 1935423941879 (7 : ZMod 1935423941879)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (57791, 1), (2392147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (57791, 1), (2392147, 1)] : List FactorBlock).map factorBlockValue).prod) = 1935423941879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_57791
      · exact prime_sixtySevenBM_2392147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1935423941879) ^ 967711970939 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1935423941879) ^ 276489134554 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1935423941879) ^ 33490058 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1935423941879) ^ 809074 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1956807057427 : Nat.Prime 1956807057427 := by
  apply lucas_primality 1956807057427 (3 : ZMod 1956807057427)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (25087269967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (25087269967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1956807057427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_25087269967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1956807057427) ^ 978403528713 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1956807057427) ^ 652269019142 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1956807057427) ^ 150523619802 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1956807057427) ^ 78 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2482718683069 : Nat.Prime 2482718683069 := by
  apply lucas_primality 2482718683069 (10 : ZMod 2482718683069)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (19, 1), (279208129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (19, 1), (279208129, 1)] : List FactorBlock).map factorBlockValue).prod) = 2482718683069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_279208129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2482718683069) ^ 1241359341534 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2482718683069) ^ 827572894356 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2482718683069) ^ 190978360236 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2482718683069) ^ 130669404372 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2482718683069) ^ 8892 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3055777873997 : Nat.Prime 3055777873997 := by
  apply lucas_primality 3055777873997 (2 : ZMod 3055777873997)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4013, 1), (190367423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4013, 1), (190367423, 1)] : List FactorBlock).map factorBlockValue).prod) = 3055777873997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_4013
      · exact prime_sixtySevenBM_190367423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3055777873997) ^ 1527888936998 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3055777873997) ^ 761469692 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3055777873997) ^ 16052 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3378826014653 : Nat.Prime 3378826014653 := by
  apply lucas_primality 3378826014653 (2 : ZMod 3378826014653)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (263, 1), (353, 1), (827147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (263, 1), (353, 1), (827147, 1)] : List FactorBlock).map factorBlockValue).prod) = 3378826014653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_263
      · exact prime_sixtySevenBM_353
      · exact prime_sixtySevenBM_827147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3378826014653) ^ 1689413007326 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378826014653) ^ 307166001332 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378826014653) ^ 12847247204 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378826014653) ^ 9571745084 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378826014653) ^ 4084916 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3870847883759 : Nat.Prime 3870847883759 := by
  apply lucas_primality 3870847883759 (19 : ZMod 3870847883759)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1935423941879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1935423941879, 1)] : List FactorBlock).map factorBlockValue).prod) = 3870847883759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_1935423941879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (19 : ZMod 3870847883759) ^ 1935423941879 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 3870847883759) ^ 2 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4401351182681 : Nat.Prime 4401351182681 := by
  apply lucas_primality 4401351182681 (3 : ZMod 4401351182681)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (215507, 1), (510581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (215507, 1), (510581, 1)] : List FactorBlock).map factorBlockValue).prod) = 4401351182681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_215507
      · exact prime_sixtySevenBM_510581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4401351182681) ^ 2200675591340 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401351182681) ^ 880270236536 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401351182681) ^ 20423240 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401351182681) ^ 8620280 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_5513643678589 : Nat.Prime 5513643678589 := by
  apply lucas_primality 5513643678589 (2 : ZMod 5513643678589)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (28927, 1), (15883787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (28927, 1), (15883787, 1)] : List FactorBlock).map factorBlockValue).prod) = 5513643678589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_28927
      · exact prime_sixtySevenBM_15883787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5513643678589) ^ 2756821839294 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5513643678589) ^ 1837881226196 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5513643678589) ^ 190605444 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5513643678589) ^ 347124 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_8566006710103 : Nat.Prime 8566006710103 := by
  apply lucas_primality 8566006710103 (19 : ZMod 8566006710103)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (161641, 1), (8832337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (161641, 1), (8832337, 1)] : List FactorBlock).map factorBlockValue).prod) = 8566006710103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_161641
      · exact prime_sixtySevenBM_8832337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 8566006710103) ^ 4283003355051 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 8566006710103) ^ 2855335570034 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 8566006710103) ^ 52994022 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 8566006710103) ^ 969846 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_9299694073097 : Nat.Prime 9299694073097 := by
  apply lucas_primality 9299694073097 (3 : ZMod 9299694073097)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (166065965591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (166065965591, 1)] : List FactorBlock).map factorBlockValue).prod) = 9299694073097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_166065965591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9299694073097) ^ 4649847036548 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299694073097) ^ 1328527724728 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299694073097) ^ 56 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_9930874732277 : Nat.Prime 9930874732277 := by
  apply lucas_primality 9930874732277 (2 : ZMod 9930874732277)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2482718683069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2482718683069, 1)] : List FactorBlock).map factorBlockValue).prod) = 9930874732277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_2482718683069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9930874732277) ^ 4965437366138 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9930874732277) ^ 4 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_10419915101249 : Nat.Prime 10419915101249 := by
  apply lucas_primality 10419915101249 (3 : ZMod 10419915101249)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (433, 1), (376007329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (433, 1), (376007329, 1)] : List FactorBlock).map factorBlockValue).prod) = 10419915101249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_433
      · exact prime_sixtySevenBM_376007329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10419915101249) ^ 5209957550624 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10419915101249) ^ 24064469056 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10419915101249) ^ 27712 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_13637295799187 : Nat.Prime 13637295799187 := by
  apply lucas_primality 13637295799187 (2 : ZMod 13637295799187)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (35699727223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (35699727223, 1)] : List FactorBlock).map factorBlockValue).prod) = 13637295799187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_191
      · exact prime_sixtySevenBM_35699727223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13637295799187) ^ 6818647899593 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13637295799187) ^ 71399454446 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13637295799187) ^ 382 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_17976511895113 : Nat.Prime 17976511895113 := by
  apply lucas_primality 17976511895113 (5 : ZMod 17976511895113)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (83, 1), (277, 1), (3619877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (83, 1), (277, 1), (3619877, 1)] : List FactorBlock).map factorBlockValue).prod) = 17976511895113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_83
      · exact prime_sixtySevenBM_277
      · exact prime_sixtySevenBM_3619877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17976511895113) ^ 8988255947556 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17976511895113) ^ 5992170631704 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17976511895113) ^ 216584480664 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17976511895113) ^ 64897154856 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17976511895113) ^ 4966056 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_18676069223321 : Nat.Prime 18676069223321 := by
  apply lucas_primality 18676069223321 (3 : ZMod 18676069223321)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (10858179781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (10858179781, 1)] : List FactorBlock).map factorBlockValue).prod) = 18676069223321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_43
      · exact prime_sixtySevenBM_10858179781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18676069223321) ^ 9338034611660 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18676069223321) ^ 3735213844664 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18676069223321) ^ 434327191240 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 18676069223321) ^ 1720 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_19095137887927 : Nat.Prime 19095137887927 := by
  apply lucas_primality 19095137887927 (19 : ZMod 19095137887927)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (101627, 1), (192121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (101627, 1), (192121, 1)] : List FactorBlock).map factorBlockValue).prod) = 19095137887927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_163
      · exact prime_sixtySevenBM_101627
      · exact prime_sixtySevenBM_192121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 19095137887927) ^ 9547568943963 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 19095137887927) ^ 6365045962642 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 19095137887927) ^ 117148085202 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 19095137887927) ^ 187894338 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 19095137887927) ^ 99391206 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_20295744354419 : Nat.Prime 20295744354419 := by
  apply lucas_primality 20295744354419 (2 : ZMod 20295744354419)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (73, 1), (233, 1), (641, 1), (71597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (73, 1), (233, 1), (641, 1), (71597, 1)] : List FactorBlock).map factorBlockValue).prod) = 20295744354419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_73
      · exact prime_sixtySevenBM_233
      · exact prime_sixtySevenBM_641
      · exact prime_sixtySevenBM_71597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20295744354419) ^ 10147872177209 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20295744354419) ^ 1561211104186 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20295744354419) ^ 278023895266 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20295744354419) ^ 87106198946 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20295744354419) ^ 31662627698 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20295744354419) ^ 283471994 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_30941892531091 : Nat.Prime 30941892531091 := by
  apply lucas_primality 30941892531091 (3 : ZMod 30941892531091)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (79, 1), (1450627873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (79, 1), (1450627873, 1)] : List FactorBlock).map factorBlockValue).prod) = 30941892531091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_79
      · exact prime_sixtySevenBM_1450627873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30941892531091) ^ 15470946265545 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30941892531091) ^ 10313964177030 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30941892531091) ^ 6188378506218 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30941892531091) ^ 391669525710 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 30941892531091) ^ 21330 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_30960957157519 : Nat.Prime 30960957157519 := by
  apply lucas_primality 30960957157519 (6 : ZMod 30960957157519)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (23, 1), (157, 1), (75211117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (23, 1), (157, 1), (75211117, 1)] : List FactorBlock).map factorBlockValue).prod) = 30960957157519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_157
      · exact prime_sixtySevenBM_75211117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 30960957157519) ^ 15480478578759 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 30960957157519) ^ 10320319052506 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 30960957157519) ^ 1629524060922 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 30960957157519) ^ 1346128572066 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 30960957157519) ^ 197203548774 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 30960957157519) ^ 411654 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_31897870031441 : Nat.Prime 31897870031441 := by
  apply lucas_primality 31897870031441 (3 : ZMod 31897870031441)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (56960482199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (56960482199, 1)] : List FactorBlock).map factorBlockValue).prod) = 31897870031441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_56960482199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31897870031441) ^ 15948935015720 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 31897870031441) ^ 6379574006288 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 31897870031441) ^ 4556838575920 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 31897870031441) ^ 560 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_39535090806833 : Nat.Prime 39535090806833 := by
  apply lucas_primality 39535090806833 (3 : ZMod 39535090806833)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (18523, 1), (133398649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (18523, 1), (133398649, 1)] : List FactorBlock).map factorBlockValue).prod) = 39535090806833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_18523
      · exact prime_sixtySevenBM_133398649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 39535090806833) ^ 19767545403416 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 39535090806833) ^ 2134378384 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 39535090806833) ^ 296368 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_40591488708839 : Nat.Prime 40591488708839 := by
  apply lucas_primality 40591488708839 (17 : ZMod 40591488708839)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20295744354419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20295744354419, 1)] : List FactorBlock).map factorBlockValue).prod) = 40591488708839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_20295744354419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 40591488708839) ^ 20295744354419 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 40591488708839) ^ 2 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_97924767070033 : Nat.Prime 97924767070033 := by
  apply lucas_primality 97924767070033 (5 : ZMod 97924767070033)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (31, 1), (15473, 1), (67511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (31, 1), (15473, 1), (67511, 1)] : List FactorBlock).map factorBlockValue).prod) = 97924767070033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_15473
      · exact prime_sixtySevenBM_67511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97924767070033) ^ 48962383535016 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97924767070033) ^ 32641589023344 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97924767070033) ^ 13989252438576 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97924767070033) ^ 3158863453872 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97924767070033) ^ 6328751184 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 97924767070033) ^ 1450500912 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_97978695745421 : Nat.Prime 97978695745421 := by
  apply lucas_primality 97978695745421 (3 : ZMod 97978695745421)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (97, 1), (40897, 1), (176417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (97, 1), (40897, 1), (176417, 1)] : List FactorBlock).map factorBlockValue).prod) = 97978695745421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_97
      · exact prime_sixtySevenBM_40897
      · exact prime_sixtySevenBM_176417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 97978695745421) ^ 48989347872710 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 97978695745421) ^ 19595739149084 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 97978695745421) ^ 13996956535060 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 97978695745421) ^ 1010089646860 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 97978695745421) ^ 2395742860 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 97978695745421) ^ 555381260 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_134067935053193 : Nat.Prime 134067935053193 := by
  apply lucas_primality 134067935053193 (3 : ZMod 134067935053193)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (17, 1), (61, 1), (1523, 1), (216551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (17, 1), (61, 1), (1523, 1), (216551, 1)] : List FactorBlock).map factorBlockValue).prod) = 134067935053193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_1523
      · exact prime_sixtySevenBM_216551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 134067935053193) ^ 67033967526596 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 134067935053193) ^ 19152562150456 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 134067935053193) ^ 7886349120776 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 134067935053193) ^ 2197835000872 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 134067935053193) ^ 88028847704 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 134067935053193) ^ 619105592 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_171528855320267 : Nat.Prime 171528855320267 := by
  apply lucas_primality 171528855320267 (2 : ZMod 171528855320267)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (83, 1), (359, 1), (169311217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (83, 1), (359, 1), (169311217, 1)] : List FactorBlock).map factorBlockValue).prod) = 171528855320267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_83
      · exact prime_sixtySevenBM_359
      · exact prime_sixtySevenBM_169311217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171528855320267) ^ 85764427660133 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 171528855320267) ^ 10089932665898 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 171528855320267) ^ 2066612714702 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 171528855320267) ^ 477796254374 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 171528855320267) ^ 1013098 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_195957391490843 : Nat.Prime 195957391490843 := by
  apply lucas_primality 195957391490843 (2 : ZMod 195957391490843)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97978695745421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97978695745421, 1)] : List FactorBlock).map factorBlockValue).prod) = 195957391490843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_97978695745421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 195957391490843) ^ 97978695745421 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 195957391490843) ^ 2 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_216092360793223 : Nat.Prime 216092360793223 := by
  apply lucas_primality 216092360793223 (3 : ZMod 216092360793223)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (26891, 1), (446436769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (26891, 1), (446436769, 1)] : List FactorBlock).map factorBlockValue).prod) = 216092360793223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_26891
      · exact prime_sixtySevenBM_446436769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 216092360793223) ^ 108046180396611 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 216092360793223) ^ 72030786931074 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 216092360793223) ^ 8035861842 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 216092360793223) ^ 484038 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_224702833587329 : Nat.Prime 224702833587329 := by
  apply lucas_primality 224702833587329 (3 : ZMod 224702833587329)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (269, 1), (21799, 1), (299371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (269, 1), (21799, 1), (299371, 1)] : List FactorBlock).map factorBlockValue).prod) = 224702833587329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_269
      · exact prime_sixtySevenBM_21799
      · exact prime_sixtySevenBM_299371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 224702833587329) ^ 112351416793664 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 224702833587329) ^ 835326518912 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 224702833587329) ^ 10307942272 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 224702833587329) ^ 750583168 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_281463233802757 : Nat.Prime 281463233802757 := by
  apply lucas_primality 281463233802757 (2 : ZMod 281463233802757)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1451, 1), (5011, 1), (3225883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1451, 1), (5011, 1), (3225883, 1)] : List FactorBlock).map factorBlockValue).prod) = 281463233802757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1451
      · exact prime_sixtySevenBM_5011
      · exact prime_sixtySevenBM_3225883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 281463233802757) ^ 140731616901378 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 281463233802757) ^ 93821077934252 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 281463233802757) ^ 193978796556 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 281463233802757) ^ 56169074796 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 281463233802757) ^ 87251532 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_321271185986549 : Nat.Prime 321271185986549 := by
  apply lucas_primality 321271185986549 (2 : ZMod 321271185986549)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (1639138704013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (1639138704013, 1)] : List FactorBlock).map factorBlockValue).prod) = 321271185986549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_1639138704013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 321271185986549) ^ 160635592993274 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 321271185986549) ^ 45895883712364 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 321271185986549) ^ 196 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_324731909670713 : Nat.Prime 324731909670713 := by
  apply lucas_primality 324731909670713 (3 : ZMod 324731909670713)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40591488708839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40591488708839, 1)] : List FactorBlock).map factorBlockValue).prod) = 324731909670713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_40591488708839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 324731909670713) ^ 162365954835356 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 324731909670713) ^ 8 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_452197439229401 : Nat.Prime 452197439229401 := by
  apply lucas_primality 452197439229401 (3 : ZMod 452197439229401)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (19, 2), (269, 1), (487, 1), (47809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (19, 2), (269, 1), (487, 1), (47809, 1)] : List FactorBlock).map factorBlockValue).prod) = 452197439229401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_269
      · exact prime_sixtySevenBM_487
      · exact prime_sixtySevenBM_47809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 452197439229401) ^ 226098719614700 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 452197439229401) ^ 90439487845880 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 452197439229401) ^ 23799865222600 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 452197439229401) ^ 1681031372600 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 452197439229401) ^ 928536836200 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 452197439229401) ^ 9458416600 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_466607860644923 : Nat.Prime 466607860644923 := by
  apply lucas_primality 466607860644923 (2 : ZMod 466607860644923)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (271, 1), (26681, 1), (32266411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (271, 1), (26681, 1), (32266411, 1)] : List FactorBlock).map factorBlockValue).prod) = 466607860644923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_271
      · exact prime_sixtySevenBM_26681
      · exact prime_sixtySevenBM_32266411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 466607860644923) ^ 233303930322461 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 466607860644923) ^ 1721800223782 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 466607860644923) ^ 17488394762 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 466607860644923) ^ 14461102 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_522220829895959 : Nat.Prime 522220829895959 := by
  apply lucas_primality 522220829895959 (23 : ZMod 522220829895959)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11587, 1), (22534773017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11587, 1), (22534773017, 1)] : List FactorBlock).map factorBlockValue).prod) = 522220829895959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_11587
      · exact prime_sixtySevenBM_22534773017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 522220829895959) ^ 261110414947979 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (23 : ZMod 522220829895959) ^ 45069546034 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (23 : ZMod 522220829895959) ^ 23174 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_593603656928441 : Nat.Prime 593603656928441 := by
  apply lucas_primality 593603656928441 (3 : ZMod 593603656928441)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (139, 1), (91811, 1), (1162859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (139, 1), (91811, 1), (1162859, 1)] : List FactorBlock).map factorBlockValue).prod) = 593603656928441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_139
      · exact prime_sixtySevenBM_91811
      · exact prime_sixtySevenBM_1162859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 593603656928441) ^ 296801828464220 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 593603656928441) ^ 118720731385688 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 593603656928441) ^ 4270529905960 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 593603656928441) ^ 6465496040 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 593603656928441) ^ 510469160 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_687424963965373 : Nat.Prime 687424963965373 := by
  apply lucas_primality 687424963965373 (2 : ZMod 687424963965373)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19095137887927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19095137887927, 1)] : List FactorBlock).map factorBlockValue).prod) = 687424963965373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_19095137887927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 687424963965373) ^ 343712481982686 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 687424963965373) ^ 229141654655124 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 687424963965373) ^ 36 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_704865714888523 : Nat.Prime 704865714888523 := by
  apply lucas_primality 704865714888523 (2 : ZMod 704865714888523)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (970889414447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (970889414447, 1)] : List FactorBlock).map factorBlockValue).prod) = 704865714888523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_970889414447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 704865714888523) ^ 352432857444261 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704865714888523) ^ 234955238296174 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704865714888523) ^ 64078701353502 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704865714888523) ^ 726 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_878494763809781 : Nat.Prime 878494763809781 := by
  apply lucas_primality 878494763809781 (3 : ZMod 878494763809781)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (3378826014653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (3378826014653, 1)] : List FactorBlock).map factorBlockValue).prod) = 878494763809781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_3378826014653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 878494763809781) ^ 439247381904890 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 878494763809781) ^ 175698952761956 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 878494763809781) ^ 67576520293060 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 878494763809781) ^ 260 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1380489694445963 : Nat.Prime 1380489694445963 := by
  apply lucas_primality 1380489694445963 (2 : ZMod 1380489694445963)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1291, 1), (534659060591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1291, 1), (534659060591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1380489694445963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_1291
      · exact prime_sixtySevenBM_534659060591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1380489694445963) ^ 690244847222981 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1380489694445963) ^ 1069318121182 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1380489694445963) ^ 2582 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3015190472409491 : Nat.Prime 3015190472409491 := by
  apply lucas_primality 3015190472409491 (2 : ZMod 3015190472409491)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (181, 1), (25703, 1), (1378969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (181, 1), (25703, 1), (1378969, 1)] : List FactorBlock).map factorBlockValue).prod) = 3015190472409491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_47
      · exact prime_sixtySevenBM_181
      · exact prime_sixtySevenBM_25703
      · exact prime_sixtySevenBM_1378969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3015190472409491) ^ 1507595236204745 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3015190472409491) ^ 603038094481898 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3015190472409491) ^ 64152988774670 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3015190472409491) ^ 16658510897290 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3015190472409491) ^ 117308892830 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3015190472409491) ^ 2186554210 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3825750253978657 : Nat.Prime 3825750253978657 := by
  apply lucas_primality 3825750253978657 (10 : ZMod 3825750253978657)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (63929, 1), (207790753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (63929, 1), (207790753, 1)] : List FactorBlock).map factorBlockValue).prod) = 3825750253978657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_63929
      · exact prime_sixtySevenBM_207790753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3825750253978657) ^ 1912875126989328 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 3825750253978657) ^ 1275250084659552 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 3825750253978657) ^ 59843736864 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 3825750253978657) ^ 18411552 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4241357230352113 : Nat.Prime 4241357230352113 := by
  apply lucas_primality 4241357230352113 (5 : ZMod 4241357230352113)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (13, 1), (755227427057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (13, 1), (755227427057, 1)] : List FactorBlock).map factorBlockValue).prod) = 4241357230352113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_755227427057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4241357230352113) ^ 2120678615176056 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4241357230352113) ^ 1413785743450704 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4241357230352113) ^ 326258248488624 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4241357230352113) ^ 5616 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4941009561034919 : Nat.Prime 4941009561034919 := by
  apply lucas_primality 4941009561034919 (11 : ZMod 4941009561034919)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (9059, 1), (38958963943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (9059, 1), (38958963943, 1)] : List FactorBlock).map factorBlockValue).prod) = 4941009561034919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_9059
      · exact prime_sixtySevenBM_38958963943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4941009561034919) ^ 2470504780517459 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4941009561034919) ^ 705858508719274 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4941009561034919) ^ 545425495202 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4941009561034919) ^ 126826 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_9489161422711717 : Nat.Prime 9489161422711717 := by
  apply lucas_primality 9489161422711717 (2 : ZMod 9489161422711717)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (55219, 1), (14320495697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (55219, 1), (14320495697, 1)] : List FactorBlock).map factorBlockValue).prod) = 9489161422711717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_55219
      · exact prime_sixtySevenBM_14320495697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9489161422711717) ^ 4744580711355858 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9489161422711717) ^ 3163053807570572 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9489161422711717) ^ 171845948364 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9489161422711717) ^ 662628 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_14009746766685457 : Nat.Prime 14009746766685457 := by
  apply lucas_primality 14009746766685457 (13 : ZMod 14009746766685457)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (347, 1), (841123124801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (347, 1), (841123124801, 1)] : List FactorBlock).map factorBlockValue).prod) = 14009746766685457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_347
      · exact prime_sixtySevenBM_841123124801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 14009746766685457) ^ 7004873383342728 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14009746766685457) ^ 4669915588895152 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14009746766685457) ^ 40373909990448 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14009746766685457) ^ 16656 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_15243522101498833 : Nat.Prime 15243522101498833 := by
  apply lucas_primality 15243522101498833 (35 : ZMod 15243522101498833)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (139, 1), (157, 1), (1663, 1), (8750591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (139, 1), (157, 1), (1663, 1), (8750591, 1)] : List FactorBlock).map factorBlockValue).prod) = 15243522101498833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_139
      · exact prime_sixtySevenBM_157
      · exact prime_sixtySevenBM_1663
      · exact prime_sixtySevenBM_8750591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (35 : ZMod 15243522101498833) ^ 7621761050749416 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (35 : ZMod 15243522101498833) ^ 5081174033832944 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (35 : ZMod 15243522101498833) ^ 109665626629488 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (35 : ZMod 15243522101498833) ^ 97092497461776 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (35 : ZMod 15243522101498833) ^ 9166279074864 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (35 : ZMod 15243522101498833) ^ 1741999152 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_18353634431779771 : Nat.Prime 18353634431779771 := by
  apply lucas_primality 18353634431779771 (11 : ZMod 18353634431779771)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (139, 1), (4401351182681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (139, 1), (4401351182681, 1)] : List FactorBlock).map factorBlockValue).prod) = 18353634431779771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_139
      · exact prime_sixtySevenBM_4401351182681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18353634431779771) ^ 9176817215889885 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 18353634431779771) ^ 6117878143926590 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 18353634431779771) ^ 3670726886355954 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 18353634431779771) ^ 132040535480430 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 18353634431779771) ^ 4170 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_25683022561935593 : Nat.Prime 25683022561935593 := by
  apply lucas_primality 25683022561935593 (3 : ZMod 25683022561935593)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (271, 1), (911077, 1), (1857521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (271, 1), (911077, 1), (1857521, 1)] : List FactorBlock).map factorBlockValue).prod) = 25683022561935593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_271
      · exact prime_sixtySevenBM_911077
      · exact prime_sixtySevenBM_1857521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25683022561935593) ^ 12841511280967796 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 25683022561935593) ^ 3669003223133656 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 25683022561935593) ^ 94771300966552 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 25683022561935593) ^ 28189738696 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 25683022561935593) ^ 13826504552 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_44357375785532731 : Nat.Prime 44357375785532731 := by
  apply lucas_primality 44357375785532731 (2 : ZMod 44357375785532731)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7079, 1), (208868370229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7079, 1), (208868370229, 1)] : List FactorBlock).map factorBlockValue).prod) = 44357375785532731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7079
      · exact prime_sixtySevenBM_208868370229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44357375785532731) ^ 22178687892766365 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44357375785532731) ^ 14785791928510910 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44357375785532731) ^ 8871475157106546 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44357375785532731) ^ 6266051106870 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 44357375785532731) ^ 212370 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_61857008299978739 : Nat.Prime 61857008299978739 := by
  apply lucas_primality 61857008299978739 (2 : ZMod 61857008299978739)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (79, 1), (142601, 1), (5093549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (79, 1), (142601, 1), (5093549, 1)] : List FactorBlock).map factorBlockValue).prod) = 61857008299978739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_79
      · exact prime_sixtySevenBM_142601
      · exact prime_sixtySevenBM_5093549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61857008299978739) ^ 30928504149989369 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61857008299978739) ^ 8836715471425534 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61857008299978739) ^ 5623364390907158 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61857008299978739) ^ 783000105063022 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61857008299978739) ^ 433776819938 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61857008299978739) ^ 12144186362 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_69315246037716529 : Nat.Prime 69315246037716529 := by
  apply lucas_primality 69315246037716529 (19 : ZMod 69315246037716529)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (131, 1), (479278999597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (131, 1), (479278999597, 1)] : List FactorBlock).map factorBlockValue).prod) = 69315246037716529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_23
      · exact prime_sixtySevenBM_131
      · exact prime_sixtySevenBM_479278999597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 69315246037716529) ^ 34657623018858264 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 69315246037716529) ^ 23105082012572176 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 69315246037716529) ^ 3013706349465936 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 69315246037716529) ^ 529124015555088 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (19 : ZMod 69315246037716529) ^ 144624 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_70772992220513197 : Nat.Prime 70772992220513197 := by
  apply lucas_primality 70772992220513197 (2 : ZMod 70772992220513197)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (139, 1), (1321, 1), (10706497969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (139, 1), (1321, 1), (10706497969, 1)] : List FactorBlock).map factorBlockValue).prod) = 70772992220513197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_139
      · exact prime_sixtySevenBM_1321
      · exact prime_sixtySevenBM_10706497969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70772992220513197) ^ 35386496110256598 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70772992220513197) ^ 23590997406837732 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70772992220513197) ^ 509158217413764 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70772992220513197) ^ 53575315836876 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 70772992220513197) ^ 6610284 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_76352937661100473 : Nat.Prime 76352937661100473 := by
  apply lucas_primality 76352937661100473 (5 : ZMod 76352937661100473)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (577, 1), (5513643678589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (577, 1), (5513643678589, 1)] : List FactorBlock).map factorBlockValue).prod) = 76352937661100473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_577
      · exact prime_sixtySevenBM_5513643678589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76352937661100473) ^ 38176468830550236 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 76352937661100473) ^ 25450979220366824 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 76352937661100473) ^ 132327448286136 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 76352937661100473) ^ 13848 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_316258114971521161 : Nat.Prime 316258114971521161 := by
  apply lucas_primality 316258114971521161 (7 : ZMod 316258114971521161)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (878494763809781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (878494763809781, 1)] : List FactorBlock).map factorBlockValue).prod) = 316258114971521161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_878494763809781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 316258114971521161) ^ 158129057485760580 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 316258114971521161) ^ 105419371657173720 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 316258114971521161) ^ 63251622994304232 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 316258114971521161) ^ 360 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_505059010268331767 : Nat.Prime 505059010268331767 := by
  apply lucas_primality 505059010268331767 (5 : ZMod 505059010268331767)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2143, 1), (6577, 1), (36913, 1), (37337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2143, 1), (6577, 1), (36913, 1), (37337, 1)] : List FactorBlock).map factorBlockValue).prod) = 505059010268331767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_2143
      · exact prime_sixtySevenBM_6577
      · exact prime_sixtySevenBM_36913
      · exact prime_sixtySevenBM_37337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 505059010268331767) ^ 252529505134165883 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 505059010268331767) ^ 38850693097563982 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 505059010268331767) ^ 235678492892362 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 505059010268331767) ^ 76791699903958 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 505059010268331767) ^ 13682415687382 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 505059010268331767) ^ 13527037798118 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_539993823243244781 : Nat.Prime 539993823243244781 := by
  apply lucas_primality 539993823243244781 (2 : ZMod 539993823243244781)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (167, 2), (15870697691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (167, 2), (15870697691, 1)] : List FactorBlock).map factorBlockValue).prod) = 539993823243244781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_167
      · exact prime_sixtySevenBM_15870697691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 539993823243244781) ^ 269996911621622390 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 539993823243244781) ^ 107998764648648956 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 539993823243244781) ^ 8852357758085980 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 539993823243244781) ^ 3233495947564340 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 539993823243244781) ^ 34024580 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_591253963479944057 : Nat.Prime 591253963479944057 := by
  apply lucas_primality 591253963479944057 (3 : ZMod 591253963479944057)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (1303, 1), (1373, 1), (1733, 1), (245753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (1303, 1), (1373, 1), (1733, 1), (245753, 1)] : List FactorBlock).map factorBlockValue).prod) = 591253963479944057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_97
      · exact prime_sixtySevenBM_1303
      · exact prime_sixtySevenBM_1373
      · exact prime_sixtySevenBM_1733
      · exact prime_sixtySevenBM_245753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 591253963479944057) ^ 295626981739972028 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 591253963479944057) ^ 6095401685360248 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 591253963479944057) ^ 453763594382152 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 591253963479944057) ^ 430629252352472 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 591253963479944057) ^ 341173666174232 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 591253963479944057) ^ 2405887063352 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_621954696085624361 : Nat.Prime 621954696085624361 := by
  apply lucas_primality 621954696085624361 (3 : ZMod 621954696085624361)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (691, 1), (83227, 1), (270368737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (691, 1), (83227, 1), (270368737, 1)] : List FactorBlock).map factorBlockValue).prod) = 621954696085624361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_691
      · exact prime_sixtySevenBM_83227
      · exact prime_sixtySevenBM_270368737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 621954696085624361) ^ 310977348042812180 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 621954696085624361) ^ 124390939217124872 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 621954696085624361) ^ 900079154971960 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 621954696085624361) ^ 7472991890680 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 621954696085624361) ^ 2300394280 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_695000097794080447 : Nat.Prime 695000097794080447 := by
  apply lucas_primality 695000097794080447 (5 : ZMod 695000097794080447)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1117, 1), (10477, 1), (582229997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1117, 1), (10477, 1), (582229997, 1)] : List FactorBlock).map factorBlockValue).prod) = 695000097794080447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_1117
      · exact prime_sixtySevenBM_10477
      · exact prime_sixtySevenBM_582229997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 695000097794080447) ^ 347500048897040223 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 695000097794080447) ^ 231666699264693482 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 695000097794080447) ^ 40882358693769438 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 695000097794080447) ^ 622202415214038 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 695000097794080447) ^ 66335792478198 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 695000097794080447) ^ 1193686518 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_765854841786616271 : Nat.Prime 765854841786616271 := by
  apply lucas_primality 765854841786616271 (14 : ZMod 765854841786616271)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (149, 1), (211, 1), (187384811561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (149, 1), (211, 1), (187384811561, 1)] : List FactorBlock).map factorBlockValue).prod) = 765854841786616271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_149
      · exact prime_sixtySevenBM_211
      · exact prime_sixtySevenBM_187384811561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 765854841786616271) ^ 382927420893308135 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (14 : ZMod 765854841786616271) ^ 153170968357323254 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (14 : ZMod 765854841786616271) ^ 58911910906662790 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (14 : ZMod 765854841786616271) ^ 5139965381118230 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (14 : ZMod 765854841786616271) ^ 3629643799936570 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (14 : ZMod 765854841786616271) ^ 4087070 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_786181336987291541 : Nat.Prime 786181336987291541 := by
  apply lucas_primality 786181336987291541 (2 : ZMod 786181336987291541)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (101, 1), (8663, 1), (44926547579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (101, 1), (8663, 1), (44926547579, 1)] : List FactorBlock).map factorBlockValue).prod) = 786181336987291541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_101
      · exact prime_sixtySevenBM_8663
      · exact prime_sixtySevenBM_44926547579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 786181336987291541) ^ 393090668493645770 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 786181336987291541) ^ 157236267397458308 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 786181336987291541) ^ 7783973633537540 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 786181336987291541) ^ 90751626109580 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 786181336987291541) ^ 17499260 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_922634765723027627 : Nat.Prime 922634765723027627 := by
  apply lucas_primality 922634765723027627 (2 : ZMod 922634765723027627)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (66853, 1), (249973, 1), (378149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (66853, 1), (249973, 1), (378149, 1)] : List FactorBlock).map factorBlockValue).prod) = 922634765723027627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_73
      · exact prime_sixtySevenBM_66853
      · exact prime_sixtySevenBM_249973
      · exact prime_sixtySevenBM_378149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 922634765723027627) ^ 461317382861513813 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 922634765723027627) ^ 12638832407164762 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 922634765723027627) ^ 13800947836642 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 922634765723027627) ^ 3690937684162 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 922634765723027627) ^ 2439870965474 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1020261539992320889 : Nat.Prime 1020261539992320889 := by
  apply lucas_primality 1020261539992320889 (11 : ZMod 1020261539992320889)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (67, 1), (296749, 1), (68972269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (67, 1), (296749, 1), (68972269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1020261539992320889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_67
      · exact prime_sixtySevenBM_296749
      · exact prime_sixtySevenBM_68972269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1020261539992320889) ^ 510130769996160444 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1020261539992320889) ^ 340087179997440296 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1020261539992320889) ^ 32911662580397448 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1020261539992320889) ^ 15227784178989864 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1020261539992320889) ^ 3438129665112 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1020261539992320889) ^ 14792344152 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1351391317555131967 : Nat.Prime 1351391317555131967 := by
  apply lucas_primality 1351391317555131967 (3 : ZMod 1351391317555131967)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (41941, 1), (49267961669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (41941, 1), (49267961669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1351391317555131967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_109
      · exact prime_sixtySevenBM_41941
      · exact prime_sixtySevenBM_49267961669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1351391317555131967) ^ 675695658777565983 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1351391317555131967) ^ 450463772518377322 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1351391317555131967) ^ 12398085482157174 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1351391317555131967) ^ 32221246931526 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1351391317555131967) ^ 27429414 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2073196340019388679 : Nat.Prime 2073196340019388679 := by
  apply lucas_primality 2073196340019388679 (7 : ZMod 2073196340019388679)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (121013, 1), (8566006710103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (121013, 1), (8566006710103, 1)] : List FactorBlock).map factorBlockValue).prod) = 2073196340019388679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_121013
      · exact prime_sixtySevenBM_8566006710103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2073196340019388679) ^ 1036598170009694339 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2073196340019388679) ^ 17132013420206 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2073196340019388679) ^ 242026 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2451892985334528763 : Nat.Prime 2451892985334528763 := by
  apply lucas_primality 2451892985334528763 (3 : ZMod 2451892985334528763)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (523, 1), (577, 1), (104166820049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (523, 1), (577, 1), (104166820049, 1)] : List FactorBlock).map factorBlockValue).prod) = 2451892985334528763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_523
      · exact prime_sixtySevenBM_577
      · exact prime_sixtySevenBM_104166820049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2451892985334528763) ^ 1225946492667264381 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451892985334528763) ^ 817297661778176254 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451892985334528763) ^ 188607152718040674 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451892985334528763) ^ 4688131903125294 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451892985334528763) ^ 4249381257078906 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451892985334528763) ^ 23538138 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2592835334286766501 : Nat.Prime 2592835334286766501 := by
  apply lucas_primality 2592835334286766501 (10 : ZMod 2592835334286766501)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (31, 1), (167, 1), (333891614743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (31, 1), (167, 1), (333891614743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2592835334286766501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_167
      · exact prime_sixtySevenBM_333891614743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2592835334286766501) ^ 1296417667143383250 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2592835334286766501) ^ 864278444762255500 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2592835334286766501) ^ 518567066857353300 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2592835334286766501) ^ 83639849493121500 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2592835334286766501) ^ 15525960085549500 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2592835334286766501) ^ 7765500 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3183523515720814327 : Nat.Prime 3183523515720814327 := by
  apply lucas_primality 3183523515720814327 (3 : ZMod 3183523515720814327)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (431, 1), (6037, 1), (6578042453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (431, 1), (6037, 1), (6578042453, 1)] : List FactorBlock).map factorBlockValue).prod) = 3183523515720814327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_431
      · exact prime_sixtySevenBM_6037
      · exact prime_sixtySevenBM_6578042453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3183523515720814327) ^ 1591761757860407163 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3183523515720814327) ^ 1061174505240271442 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3183523515720814327) ^ 102694306958735946 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3183523515720814327) ^ 7386365465709546 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3183523515720814327) ^ 527335351287198 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3183523515720814327) ^ 483962142 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3434878070737578767 : Nat.Prime 3434878070737578767 := by
  apply lucas_primality 3434878070737578767 (5 : ZMod 3434878070737578767)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (10691, 1), (85081, 1), (269731939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (10691, 1), (85081, 1), (269731939, 1)] : List FactorBlock).map factorBlockValue).prod) = 3434878070737578767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_10691
      · exact prime_sixtySevenBM_85081
      · exact prime_sixtySevenBM_269731939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3434878070737578767) ^ 1717439035368789383 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3434878070737578767) ^ 490696867248225538 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3434878070737578767) ^ 321286883428826 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3434878070737578767) ^ 40371858237886 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3434878070737578767) ^ 12734413594 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3514564788775726243 : Nat.Prime 3514564788775726243 := by
  apply lucas_primality 3514564788775726243 (2 : ZMod 3514564788775726243)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (65833927, 1), (287017811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (65833927, 1), (287017811, 1)] : List FactorBlock).map factorBlockValue).prod) = 3514564788775726243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_65833927
      · exact prime_sixtySevenBM_287017811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3514564788775726243) ^ 1757282394387863121 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3514564788775726243) ^ 1171521596258575414 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3514564788775726243) ^ 113373057702442782 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3514564788775726243) ^ 53385312846 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3514564788775726243) ^ 12245110422 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_10383665573620030271 : Nat.Prime 10383665573620030271 := by
  apply lucas_primality 10383665573620030271 (13 : ZMod 10383665573620030271)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (268253, 1), (3870847883759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (268253, 1), (3870847883759, 1)] : List FactorBlock).map factorBlockValue).prod) = 10383665573620030271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_268253
      · exact prime_sixtySevenBM_3870847883759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 10383665573620030271) ^ 5191832786810015135 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 10383665573620030271) ^ 2076733114724006054 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 10383665573620030271) ^ 38708478837590 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 10383665573620030271) ^ 2682530 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_12878371604124352769 : Nat.Prime 12878371604124352769 := by
  apply lucas_primality 12878371604124352769 (3 : ZMod 12878371604124352769)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (13, 1), (157, 1), (859, 1), (28693585387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (13, 1), (157, 1), (859, 1), (28693585387, 1)] : List FactorBlock).map factorBlockValue).prod) = 12878371604124352769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_157
      · exact prime_sixtySevenBM_859
      · exact prime_sixtySevenBM_28693585387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12878371604124352769) ^ 6439185802062176384 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12878371604124352769) ^ 990643969548027136 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12878371604124352769) ^ 82027844612257024 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12878371604124352769) ^ 14992283590365952 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12878371604124352769) ^ 448824064 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_13260735532453163933 : Nat.Prime 13260735532453163933 := by
  apply lucas_primality 13260735532453163933 (2 : ZMod 13260735532453163933)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (59, 1), (97, 1), (173, 1), (4861, 1), (40519421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (59, 1), (97, 1), (173, 1), (4861, 1), (40519421, 1)] : List FactorBlock).map factorBlockValue).prod) = 13260735532453163933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_59
      · exact prime_sixtySevenBM_97
      · exact prime_sixtySevenBM_173
      · exact prime_sixtySevenBM_4861
      · exact prime_sixtySevenBM_40519421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13260735532453163933) ^ 6630367766226581966 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13260735532453163933) ^ 780043266614891996 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13260735532453163933) ^ 224758229363612948 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13260735532453163933) ^ 136708613736630556 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13260735532453163933) ^ 76651650476607884 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13260735532453163933) ^ 2727985092049612 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13260735532453163933) ^ 327268633292 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_13877939409950316691 : Nat.Prime 13877939409950316691 := by
  apply lucas_primality 13877939409950316691 (2 : ZMod 13877939409950316691)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (31, 1), (452197439229401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (31, 1), (452197439229401, 1)] : List FactorBlock).map factorBlockValue).prod) = 13877939409950316691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_452197439229401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13877939409950316691) ^ 6938969704975158345 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13877939409950316691) ^ 4625979803316772230 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13877939409950316691) ^ 2775587881990063338 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13877939409950316691) ^ 1261630855450028790 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13877939409950316691) ^ 447675464837106990 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13877939409950316691) ^ 30690 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_14151264065771247739 : Nat.Prime 14151264065771247739 := by
  apply lucas_primality 14151264065771247739 (2 : ZMod 14151264065771247739)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (786181336987291541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (786181336987291541, 1)] : List FactorBlock).map factorBlockValue).prod) = 14151264065771247739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_786181336987291541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14151264065771247739) ^ 7075632032885623869 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14151264065771247739) ^ 4717088021923749246 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14151264065771247739) ^ 18 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_22143234377352663049 : Nat.Prime 22143234377352663049 := by
  apply lucas_primality 22143234377352663049 (7 : ZMod 22143234377352663049)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (922634765723027627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (922634765723027627, 1)] : List FactorBlock).map factorBlockValue).prod) = 22143234377352663049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_922634765723027627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 22143234377352663049) ^ 11071617188676331524 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 22143234377352663049) ^ 7381078125784221016 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 22143234377352663049) ^ 24 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_23842584034696536511 : Nat.Prime 23842584034696536511 := by
  apply lucas_primality 23842584034696536511 (3 : ZMod 23842584034696536511)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (479, 1), (1453, 1), (1141907537291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (479, 1), (1453, 1), (1141907537291, 1)] : List FactorBlock).map factorBlockValue).prod) = 23842584034696536511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_479
      · exact prime_sixtySevenBM_1453
      · exact prime_sixtySevenBM_1141907537291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23842584034696536511) ^ 11921292017348268255 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 23842584034696536511) ^ 7947528011565512170 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 23842584034696536511) ^ 4768516806939307302 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 23842584034696536511) ^ 49775749550514690 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 23842584034696536511) ^ 16409211310871670 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 23842584034696536511) ^ 20879610 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_24325043715992375407 : Nat.Prime 24325043715992375407 := by
  apply lucas_primality 24325043715992375407 (3 : ZMod 24325043715992375407)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1351391317555131967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1351391317555131967, 1)] : List FactorBlock).map factorBlockValue).prod) = 24325043715992375407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1351391317555131967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24325043715992375407) ^ 12162521857996187703 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 24325043715992375407) ^ 8108347905330791802 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 24325043715992375407) ^ 18 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_24486276959815701337 : Nat.Prime 24486276959815701337 := by
  apply lucas_primality 24486276959815701337 (5 : ZMod 24486276959815701337)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1020261539992320889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1020261539992320889, 1)] : List FactorBlock).map factorBlockValue).prod) = 24486276959815701337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1020261539992320889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24486276959815701337) ^ 12243138479907850668 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24486276959815701337) ^ 8162092319938567112 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 24486276959815701337) ^ 24 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_26132105082422367101 : Nat.Prime 26132105082422367101 := by
  apply lucas_primality 26132105082422367101 (3 : ZMod 26132105082422367101)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (809, 1), (10419915101249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (809, 1), (10419915101249, 1)] : List FactorBlock).map factorBlockValue).prod) = 26132105082422367101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_809
      · exact prime_sixtySevenBM_10419915101249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26132105082422367101) ^ 13066052541211183550 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26132105082422367101) ^ 5226421016484473420 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26132105082422367101) ^ 842971131691044100 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26132105082422367101) ^ 32301736813871900 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26132105082422367101) ^ 2507900 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_32784214398988731671 : Nat.Prime 32784214398988731671 := by
  apply lucas_primality 32784214398988731671 (11 : ZMod 32784214398988731671)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (61857008299978739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (61857008299978739, 1)] : List FactorBlock).map factorBlockValue).prod) = 32784214398988731671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_53
      · exact prime_sixtySevenBM_61857008299978739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 32784214398988731671) ^ 16392107199494365835 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 32784214398988731671) ^ 6556842879797746334 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 32784214398988731671) ^ 618570082999787390 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (11 : ZMod 32784214398988731671) ^ 530 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_40912830304610994361 : Nat.Prime 40912830304610994361 := by
  apply lucas_primality 40912830304610994361 (17 : ZMod 40912830304610994361)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (421, 1), (235979, 1), (381311863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (421, 1), (235979, 1), (381311863, 1)] : List FactorBlock).map factorBlockValue).prod) = 40912830304610994361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_421
      · exact prime_sixtySevenBM_235979
      · exact prime_sixtySevenBM_381311863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 40912830304610994361) ^ 20456415152305497180 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 40912830304610994361) ^ 13637610101536998120 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 40912830304610994361) ^ 8182566060922198872 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 40912830304610994361) ^ 97180119488387160 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 40912830304610994361) ^ 173374877868840 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (17 : ZMod 40912830304610994361) ^ 107294931720 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_44287931726702443993 : Nat.Prime 44287931726702443993 := by
  apply lucas_primality 44287931726702443993 (15 : ZMod 44287931726702443993)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (20707, 1), (1259393, 1), (70761283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (20707, 1), (1259393, 1), (70761283, 1)] : List FactorBlock).map factorBlockValue).prod) = 44287931726702443993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_20707
      · exact prime_sixtySevenBM_1259393
      · exact prime_sixtySevenBM_70761283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 44287931726702443993) ^ 22143965863351221996 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (15 : ZMod 44287931726702443993) ^ 14762643908900814664 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (15 : ZMod 44287931726702443993) ^ 2138790347549256 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (15 : ZMod 44287931726702443993) ^ 35166093289944 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (15 : ZMod 44287931726702443993) ^ 625878020424 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_45001547397723669293 : Nat.Prime 45001547397723669293 := by
  apply lucas_primality 45001547397723669293 (2 : ZMod 45001547397723669293)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (6287, 1), (329683, 1), (102412171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (6287, 1), (329683, 1), (102412171, 1)] : List FactorBlock).map factorBlockValue).prod) = 45001547397723669293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_53
      · exact prime_sixtySevenBM_6287
      · exact prime_sixtySevenBM_329683
      · exact prime_sixtySevenBM_102412171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45001547397723669293) ^ 22500773698861834646 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45001547397723669293) ^ 849085799957050364 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45001547397723669293) ^ 7157872975620116 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45001547397723669293) ^ 136499447644324 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45001547397723669293) ^ 439416008452 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_90003094795447338587 : Nat.Prime 90003094795447338587 := by
  apply lucas_primality 90003094795447338587 (2 : ZMod 90003094795447338587)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (45001547397723669293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (45001547397723669293, 1)] : List FactorBlock).map factorBlockValue).prod) = 90003094795447338587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_45001547397723669293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 90003094795447338587) ^ 45001547397723669293 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 90003094795447338587) ^ 2 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_259308625426292780171 : Nat.Prime 259308625426292780171 := by
  apply lucas_primality 259308625426292780171 (2 : ZMod 259308625426292780171)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (60589, 1), (4949951, 1), (12351629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (60589, 1), (4949951, 1), (12351629, 1)] : List FactorBlock).map factorBlockValue).prod) = 259308625426292780171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_60589
      · exact prime_sixtySevenBM_4949951
      · exact prime_sixtySevenBM_12351629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259308625426292780171) ^ 129654312713146390085 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259308625426292780171) ^ 51861725085258556034 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259308625426292780171) ^ 37044089346613254310 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259308625426292780171) ^ 4279797082412530 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259308625426292780171) ^ 52386099463670 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259308625426292780171) ^ 20993880679730 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_325823755667821133017 : Nat.Prime 325823755667821133017 := by
  apply lucas_primality 325823755667821133017 (20 : ZMod 325823755667821133017)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (765950309, 1), (2532053443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (765950309, 1), (2532053443, 1)] : List FactorBlock).map factorBlockValue).prod) = 325823755667821133017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_765950309
      · exact prime_sixtySevenBM_2532053443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (20 : ZMod 325823755667821133017) ^ 162911877833910566508 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (20 : ZMod 325823755667821133017) ^ 108607918555940377672 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (20 : ZMod 325823755667821133017) ^ 46546250809688733288 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (20 : ZMod 325823755667821133017) ^ 425384978424 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (20 : ZMod 325823755667821133017) ^ 128679651912 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_472943527470990309857 : Nat.Prime 472943527470990309857 := by
  apply lucas_primality 472943527470990309857 (3 : ZMod 472943527470990309857)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (557, 1), (11198879, 1), (2369351861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (557, 1), (11198879, 1), (2369351861, 1)] : List FactorBlock).map factorBlockValue).prod) = 472943527470990309857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_557
      · exact prime_sixtySevenBM_11198879
      · exact prime_sixtySevenBM_2369351861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 472943527470990309857) ^ 236471763735495154928 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 472943527470990309857) ^ 849090713592442208 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 472943527470990309857) ^ 42231327570464 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 472943527470990309857) ^ 199608819296 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1835916006343368973577 : Nat.Prime 1835916006343368973577 := by
  apply lucas_primality 1835916006343368973577 (3 : ZMod 1835916006343368973577)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (32784214398988731671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (32784214398988731671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1835916006343368973577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_32784214398988731671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1835916006343368973577) ^ 917958003171684486788 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1835916006343368973577) ^ 262273715191909853368 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1835916006343368973577) ^ 56 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2313846981577503582953 : Nat.Prime 2313846981577503582953 := by
  apply lucas_primality 2313846981577503582953 (5 : ZMod 2313846981577503582953)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (101, 1), (39583751, 1), (10334947817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (101, 1), (39583751, 1), (10334947817, 1)] : List FactorBlock).map factorBlockValue).prod) = 2313846981577503582953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_101
      · exact prime_sixtySevenBM_39583751
      · exact prime_sixtySevenBM_10334947817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2313846981577503582953) ^ 1156923490788751791476 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2313846981577503582953) ^ 330549568796786226136 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2313846981577503582953) ^ 22909376055222807752 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2313846981577503582953) ^ 58454464852952 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2313846981577503582953) ^ 223885695656 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3309911888690030779789 : Nat.Prime 3309911888690030779789 := by
  apply lucas_primality 3309911888690030779789 (6 : ZMod 3309911888690030779789)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (127, 1), (149, 1), (1213, 1), (1951, 1), (56506789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (127, 1), (149, 1), (1213, 1), (1951, 1), (56506789, 1)] : List FactorBlock).map factorBlockValue).prod) = 3309911888690030779789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_109
      · exact prime_sixtySevenBM_127
      · exact prime_sixtySevenBM_149
      · exact prime_sixtySevenBM_1213
      · exact prime_sixtySevenBM_1951
      · exact prime_sixtySevenBM_56506789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3309911888690030779789) ^ 1654955944345015389894 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3309911888690030779789) ^ 1103303962896676926596 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3309911888690030779789) ^ 30366164116422300732 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3309911888690030779789) ^ 26062298336141974644 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3309911888690030779789) ^ 22214173749597522012 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3309911888690030779789) ^ 2728699001393265276 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3309911888690030779789) ^ 1696520701532563188 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3309911888690030779789) ^ 58575472916892 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_3667521671472734247869 : Nat.Prime 3667521671472734247869 := by
  apply lucas_primality 3667521671472734247869 (2 : ZMod 3667521671472734247869)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (797, 1), (83653, 1), (205257035861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (797, 1), (83653, 1), (205257035861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3667521671472734247869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_67
      · exact prime_sixtySevenBM_797
      · exact prime_sixtySevenBM_83653
      · exact prime_sixtySevenBM_205257035861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3667521671472734247869) ^ 1833760835736367123934 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3667521671472734247869) ^ 54739129424966182804 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3667521671472734247869) ^ 4601658307995902444 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3667521671472734247869) ^ 43842081831766156 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3667521671472734247869) ^ 17867946188 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_8512983494477825577427 : Nat.Prime 8512983494477825577427 := by
  apply lucas_primality 8512983494477825577427 (2 : ZMod 8512983494477825577427)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (472943527470990309857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (472943527470990309857, 1)] : List FactorBlock).map factorBlockValue).prod) = 8512983494477825577427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_472943527470990309857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8512983494477825577427) ^ 4256491747238912788713 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8512983494477825577427) ^ 2837661164825941859142 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8512983494477825577427) ^ 18 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_11763877546139427185579 : Nat.Prime 11763877546139427185579 := by
  apply lucas_primality 11763877546139427185579 (2 : ZMod 11763877546139427185579)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12605743, 1), (466607860644923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12605743, 1), (466607860644923, 1)] : List FactorBlock).map factorBlockValue).prod) = 11763877546139427185579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_12605743
      · exact prime_sixtySevenBM_466607860644923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11763877546139427185579) ^ 5881938773069713592789 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11763877546139427185579) ^ 933215721289846 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11763877546139427185579) ^ 25211486 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_12624316721282408664857 : Nat.Prime 12624316721282408664857 := by
  apply lucas_primality 12624316721282408664857 (3 : ZMod 12624316721282408664857)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (449, 1), (3514564788775726243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (449, 1), (3514564788775726243, 1)] : List FactorBlock).map factorBlockValue).prod) = 12624316721282408664857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_449
      · exact prime_sixtySevenBM_3514564788775726243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12624316721282408664857) ^ 6312158360641204332428 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12624316721282408664857) ^ 28116518310205809944 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12624316721282408664857) ^ 3592 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_22560693613031373379373 : Nat.Prime 22560693613031373379373 := by
  apply lucas_primality 22560693613031373379373 (2 : ZMod 22560693613031373379373)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (9781, 1), (44357375785532731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (9781, 1), (44357375785532731, 1)] : List FactorBlock).map factorBlockValue).prod) = 22560693613031373379373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_13
      · exact prime_sixtySevenBM_9781
      · exact prime_sixtySevenBM_44357375785532731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22560693613031373379373) ^ 11280346806515686689686 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 22560693613031373379373) ^ 1735437970233182567644 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 22560693613031373379373) ^ 2306583540847702012 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 22560693613031373379373) ^ 508612 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_30623335438328980107197 : Nat.Prime 30623335438328980107197 := by
  apply lucas_primality 30623335438328980107197 (2 : ZMod 30623335438328980107197)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (541, 1), (14151264065771247739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (541, 1), (14151264065771247739, 1)] : List FactorBlock).map factorBlockValue).prod) = 30623335438328980107197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_541
      · exact prime_sixtySevenBM_14151264065771247739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30623335438328980107197) ^ 15311667719164490053598 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30623335438328980107197) ^ 56605056263084990956 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30623335438328980107197) ^ 2164 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_61296126723802617945047 : Nat.Prime 61296126723802617945047 := by
  apply lucas_primality 61296126723802617945047 (5 : ZMod 61296126723802617945047)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1452079, 1), (3015190472409491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1452079, 1), (3015190472409491, 1)] : List FactorBlock).map factorBlockValue).prod) = 61296126723802617945047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_1452079
      · exact prime_sixtySevenBM_3015190472409491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61296126723802617945047) ^ 30648063361901308972523 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 61296126723802617945047) ^ 8756589531971802563578 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 61296126723802617945047) ^ 42212666613732874 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 61296126723802617945047) ^ 20329106 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_66248007409036892366699 : Nat.Prime 66248007409036892366699 := by
  apply lucas_primality 66248007409036892366699 (2 : ZMod 66248007409036892366699)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1279, 1), (5869, 1), (940981, 1), (4689508379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1279, 1), (5869, 1), (940981, 1), (4689508379, 1)] : List FactorBlock).map factorBlockValue).prod) = 66248007409036892366699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_1279
      · exact prime_sixtySevenBM_5869
      · exact prime_sixtySevenBM_940981
      · exact prime_sixtySevenBM_4689508379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66248007409036892366699) ^ 33124003704518446183349 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66248007409036892366699) ^ 51796721977354880662 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66248007409036892366699) ^ 11287784530420325842 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66248007409036892366699) ^ 70403129722105858 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66248007409036892366699) ^ 14126855536862 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_92449439066504703737293 : Nat.Prime 92449439066504703737293 := by
  apply lucas_primality 92449439066504703737293 (2 : ZMod 92449439066504703737293)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (241, 1), (1069, 1), (10169, 1), (24859, 1), (1765597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (241, 1), (1069, 1), (10169, 1), (24859, 1), (1765597, 1)] : List FactorBlock).map factorBlockValue).prod) = 92449439066504703737293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_67
      · exact prime_sixtySevenBM_241
      · exact prime_sixtySevenBM_1069
      · exact prime_sixtySevenBM_10169
      · exact prime_sixtySevenBM_24859
      · exact prime_sixtySevenBM_1765597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92449439066504703737293) ^ 46224719533252351868646 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 92449439066504703737293) ^ 30816479688834901245764 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 92449439066504703737293) ^ 1379842374126935876676 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 92449439066504703737293) ^ 383607630981347318412 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 92449439066504703737293) ^ 86482169379330873468 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 92449439066504703737293) ^ 9091300921084148268 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 92449439066504703737293) ^ 3718952454503588388 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 92449439066504703737293) ^ 52361574621221436 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_713132280914770920120109 : Nat.Prime 713132280914770920120109 := by
  apply lucas_primality 713132280914770920120109 (2 : ZMod 713132280914770920120109)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (7869657811, 1), (444205651507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (7869657811, 1), (444205651507, 1)] : List FactorBlock).map factorBlockValue).prod) = 713132280914770920120109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_7869657811
      · exact prime_sixtySevenBM_444205651507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 713132280914770920120109) ^ 356566140457385460060054 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 713132280914770920120109) ^ 237710760304923640040036 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 713132280914770920120109) ^ 41948957700868877654124 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 713132280914770920120109) ^ 90617952907428 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 713132280914770920120109) ^ 1605410193444 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1237183038685676049155987 : Nat.Prime 1237183038685676049155987 := by
  apply lucas_primality 1237183038685676049155987 (2 : ZMod 1237183038685676049155987)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (12624316721282408664857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (12624316721282408664857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1237183038685676049155987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_12624316721282408664857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1237183038685676049155987) ^ 618591519342838024577993 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1237183038685676049155987) ^ 176740434097953721307998 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1237183038685676049155987) ^ 98 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1358577844694093040446981 : Nat.Prime 1358577844694093040446981 := by
  apply lucas_primality 1358577844694093040446981 (3 : ZMod 1358577844694093040446981)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (1835916006343368973577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (1835916006343368973577, 1)] : List FactorBlock).map factorBlockValue).prod) = 1358577844694093040446981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_37
      · exact prime_sixtySevenBM_1835916006343368973577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1358577844694093040446981) ^ 679288922347046520223490 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358577844694093040446981) ^ 271715568938818608089396 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358577844694093040446981) ^ 36718320126867379471540 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358577844694093040446981) ^ 740 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1431574518088793008083229 : Nat.Prime 1431574518088793008083229 := by
  apply lucas_primality 1431574518088793008083229 (2 : ZMod 1431574518088793008083229)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (91909, 1), (76352937661100473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (91909, 1), (76352937661100473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1431574518088793008083229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_17
      · exact prime_sixtySevenBM_91909
      · exact prime_sixtySevenBM_76352937661100473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1431574518088793008083229) ^ 715787259044396504041614 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1431574518088793008083229) ^ 477191506029597669361076 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1431574518088793008083229) ^ 84210265769929000475484 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1431574518088793008083229) ^ 15575999282864496492 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1431574518088793008083229) ^ 18749436 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_2920146030925646786229493 : Nat.Prime 2920146030925646786229493 := by
  apply lucas_primality 2920146030925646786229493 (2 : ZMod 2920146030925646786229493)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (21202421, 1), (3825750253978657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (21202421, 1), (3825750253978657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2920146030925646786229493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_21202421
      · exact prime_sixtySevenBM_3825750253978657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2920146030925646786229493) ^ 1460073015462823393114746 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2920146030925646786229493) ^ 973382010308548928743164 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2920146030925646786229493) ^ 137727009143231652 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2920146030925646786229493) ^ 763287156 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_13669004527159464145515311 : Nat.Prime 13669004527159464145515311 := by
  apply lucas_primality 13669004527159464145515311 (7 : ZMod 13669004527159464145515311)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89670907, 1), (15243522101498833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89670907, 1), (15243522101498833, 1)] : List FactorBlock).map factorBlockValue).prod) = 13669004527159464145515311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_89670907
      · exact prime_sixtySevenBM_15243522101498833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13669004527159464145515311) ^ 6834502263579732072757655 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 13669004527159464145515311) ^ 2733800905431892829103062 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 13669004527159464145515311) ^ 152435221014988330 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 13669004527159464145515311) ^ 896709070 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_22269294696342168884807767 : Nat.Prime 22269294696342168884807767 := by
  apply lucas_primality 22269294696342168884807767 (5 : ZMod 22269294696342168884807767)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1237183038685676049155987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1237183038685676049155987, 1)] : List FactorBlock).map factorBlockValue).prod) = 22269294696342168884807767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_1237183038685676049155987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 22269294696342168884807767) ^ 11134647348171084442403883 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 22269294696342168884807767) ^ 7423098232114056294935922 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 22269294696342168884807767) ^ 18 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_37364094922117497510972277 : Nat.Prime 37364094922117497510972277 := by
  apply lucas_primality 37364094922117497510972277 (5 : ZMod 37364094922117497510972277)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (101, 1), (431, 1), (23842584034696536511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (101, 1), (431, 1), (23842584034696536511, 1)] : List FactorBlock).map factorBlockValue).prod) = 37364094922117497510972277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_101
      · exact prime_sixtySevenBM_431
      · exact prime_sixtySevenBM_23842584034696536511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37364094922117497510972277) ^ 18682047461058748755486138 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 37364094922117497510972277) ^ 12454698307372499170324092 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 37364094922117497510972277) ^ 369941533882351460504676 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 37364094922117497510972277) ^ 86691635550156606753996 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 37364094922117497510972277) ^ 1567116 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_145342901348420357290387573 : Nat.Prime 145342901348420357290387573 := by
  apply lucas_primality 145342901348420357290387573 (2 : ZMod 145342901348420357290387573)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (97, 1), (641, 1), (124339, 1), (522220829895959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (97, 1), (641, 1), (124339, 1), (522220829895959, 1)] : List FactorBlock).map factorBlockValue).prod) = 145342901348420357290387573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_97
      · exact prime_sixtySevenBM_641
      · exact prime_sixtySevenBM_124339
      · exact prime_sixtySevenBM_522220829895959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 145342901348420357290387573) ^ 72671450674210178645193786 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 145342901348420357290387573) ^ 48447633782806785763462524 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 145342901348420357290387573) ^ 1498380426272374817426676 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 145342901348420357290387573) ^ 226743995863370292184692 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 145342901348420357290387573) ^ 1168924483455877538748 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 145342901348420357290387573) ^ 278316936108 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_314332862043210693346274711 : Nat.Prime 314332862043210693346274711 := by
  apply lucas_primality 314332862043210693346274711 (7 : ZMod 314332862043210693346274711)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (41, 1), (112061, 1), (621954696085624361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (41, 1), (112061, 1), (621954696085624361, 1)] : List FactorBlock).map factorBlockValue).prod) = 314332862043210693346274711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_41
      · exact prime_sixtySevenBM_112061
      · exact prime_sixtySevenBM_621954696085624361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 314332862043210693346274711) ^ 157166431021605346673137355 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 314332862043210693346274711) ^ 62866572408642138669254942 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 314332862043210693346274711) ^ 28575714731200972122388610 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 314332862043210693346274711) ^ 7666655171785626666982310 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 314332862043210693346274711) ^ 2805015679346165868110 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 314332862043210693346274711) ^ 505395110 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_455240696752236176570466823 : Nat.Prime 455240696752236176570466823 := by
  apply lucas_primality 455240696752236176570466823 (3 : ZMod 455240696752236176570466823)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (1431574518088793008083229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (1431574518088793008083229, 1)] : List FactorBlock).map factorBlockValue).prod) = 455240696752236176570466823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_53
      · exact prime_sixtySevenBM_1431574518088793008083229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 455240696752236176570466823) ^ 227620348376118088285233411 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 455240696752236176570466823) ^ 151746898917412058856822274 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 455240696752236176570466823) ^ 8589447108532758048499374 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 455240696752236176570466823) ^ 318 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_792118812348890947232612273 : Nat.Prime 792118812348890947232612273 := by
  apply lucas_primality 792118812348890947232612273 (3 : ZMod 792118812348890947232612273)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1459, 1), (1889, 1), (258403, 1), (9930874732277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1459, 1), (1889, 1), (258403, 1), (9930874732277, 1)] : List FactorBlock).map factorBlockValue).prod) = 792118812348890947232612273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_1459
      · exact prime_sixtySevenBM_1889
      · exact prime_sixtySevenBM_258403
      · exact prime_sixtySevenBM_9930874732277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 792118812348890947232612273) ^ 396059406174445473616306136 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 792118812348890947232612273) ^ 113159830335555849604658896 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 792118812348890947232612273) ^ 542918994070521553963408 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 792118812348890947232612273) ^ 419332351693430887894448 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 792118812348890947232612273) ^ 3065439690517876910224 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 792118812348890947232612273) ^ 79763246813936 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_800120012473627219426881083 : Nat.Prime 800120012473627219426881083 := by
  apply lucas_primality 800120012473627219426881083 (2 : ZMod 800120012473627219426881083)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (2920146030925646786229493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (2920146030925646786229493, 1)] : List FactorBlock).map factorBlockValue).prod) = 800120012473627219426881083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_137
      · exact prime_sixtySevenBM_2920146030925646786229493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 800120012473627219426881083) ^ 400060006236813609713440541 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 800120012473627219426881083) ^ 5840292061851293572458986 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 800120012473627219426881083) ^ 274 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1164880606395427863577370989 : Nat.Prime 1164880606395427863577370989 := by
  apply lucas_primality 1164880606395427863577370989 (2 : ZMod 1164880606395427863577370989)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (61, 1), (1093, 1), (5689, 1), (44531, 1), (522467289137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (61, 1), (1093, 1), (5689, 1), (44531, 1), (522467289137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1164880606395427863577370989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_11
      · exact prime_sixtySevenBM_61
      · exact prime_sixtySevenBM_1093
      · exact prime_sixtySevenBM_5689
      · exact prime_sixtySevenBM_44531
      · exact prime_sixtySevenBM_522467289137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1164880606395427863577370989) ^ 582440303197713931788685494 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164880606395427863577370989) ^ 388293535465142621192456996 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164880606395427863577370989) ^ 105898236945038896688851908 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164880606395427863577370989) ^ 19096403383531604320940508 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164880606395427863577370989) ^ 1065764507223630250299516 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164880606395427863577370989) ^ 204760169870878513548492 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164880606395427863577370989) ^ 26158869246040463128548 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164880606395427863577370989) ^ 2229576148814124 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1466886689534983235615948653 : Nat.Prime 1466886689534983235615948653 := by
  apply lucas_primality 1466886689534983235615948653 (2 : ZMod 1466886689534983235615948653)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (961487, 1), (4854459817, 1), (26189728399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (961487, 1), (4854459817, 1), (26189728399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1466886689534983235615948653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_961487
      · exact prime_sixtySevenBM_4854459817
      · exact prime_sixtySevenBM_26189728399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1466886689534983235615948653) ^ 733443344767491617807974326 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466886689534983235615948653) ^ 488962229844994411871982884 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466886689534983235615948653) ^ 1525643809573070915796 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466886689534983235615948653) ^ 302173000670031756 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466886689534983235615948653) ^ 56010000072814548 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1494563796884699900438891081 : Nat.Prime 1494563796884699900438891081 := by
  apply lucas_primality 1494563796884699900438891081 (6 : ZMod 1494563796884699900438891081)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37364094922117497510972277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37364094922117497510972277, 1)] : List FactorBlock).map factorBlockValue).prod) = 1494563796884699900438891081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_37364094922117497510972277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1494563796884699900438891081) ^ 747281898442349950219445540 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1494563796884699900438891081) ^ 298912759376939980087778216 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1494563796884699900438891081) ^ 40 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_1885997172259264160077648267 : Nat.Prime 1885997172259264160077648267 := by
  apply lucas_primality 1885997172259264160077648267 (2 : ZMod 1885997172259264160077648267)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (314332862043210693346274711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (314332862043210693346274711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1885997172259264160077648267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_314332862043210693346274711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1885997172259264160077648267) ^ 942998586129632080038824133 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1885997172259264160077648267) ^ 628665724086421386692549422 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1885997172259264160077648267) ^ 6 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4659522425581711454309483957 : Nat.Prime 4659522425581711454309483957 := by
  apply lucas_primality 4659522425581711454309483957 (2 : ZMod 4659522425581711454309483957)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1164880606395427863577370989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1164880606395427863577370989, 1)] : List FactorBlock).map factorBlockValue).prod) = 4659522425581711454309483957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_1164880606395427863577370989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4659522425581711454309483957) ^ 2329761212790855727154741978 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4659522425581711454309483957) ^ 4 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_4950742577180568420203826701 : Nat.Prime 4950742577180568420203826701 := by
  apply lucas_primality 4950742577180568420203826701 (3 : ZMod 4950742577180568420203826701)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (1459, 1), (1889, 1), (258403, 1), (9930874732277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (1459, 1), (1889, 1), (258403, 1), (9930874732277, 1)] : List FactorBlock).map factorBlockValue).prod) = 4950742577180568420203826701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_7
      · exact prime_sixtySevenBM_1459
      · exact prime_sixtySevenBM_1889
      · exact prime_sixtySevenBM_258403
      · exact prime_sixtySevenBM_9930874732277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4950742577180568420203826701) ^ 2475371288590284210101913350 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4950742577180568420203826701) ^ 990148515436113684040765340 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4950742577180568420203826701) ^ 707248939597224060029118100 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4950742577180568420203826701) ^ 3393243712940759712271300 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4950742577180568420203826701) ^ 2620827198083943049340300 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4950742577180568420203826701) ^ 19158998065736730688900 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4950742577180568420203826701) ^ 498520292587100 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_15842376246977818944652245443 : Nat.Prime 15842376246977818944652245443 := by
  apply lucas_primality 15842376246977818944652245443 (2 : ZMod 15842376246977818944652245443)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (13421, 1), (31319, 1), (56401, 1), (576049, 1), (13489097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (13421, 1), (31319, 1), (56401, 1), (576049, 1), (13489097, 1)] : List FactorBlock).map factorBlockValue).prod) = 15842376246977818944652245443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_43
      · exact prime_sixtySevenBM_13421
      · exact prime_sixtySevenBM_31319
      · exact prime_sixtySevenBM_56401
      · exact prime_sixtySevenBM_576049
      · exact prime_sixtySevenBM_13489097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15842376246977818944652245443) ^ 7921188123488909472326122721 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15842376246977818944652245443) ^ 368427354580879510340749894 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15842376246977818944652245443) ^ 1180416976900217490846602 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15842376246977818944652245443) ^ 505839147066567225794318 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15842376246977818944652245443) ^ 280888215580890745636642 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15842376246977818944652245443) ^ 27501785867135988335458 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15842376246977818944652245443) ^ 1174457878609503582386 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_79211881234889094723261227227 : Nat.Prime 79211881234889094723261227227 := by
  apply lucas_primality 79211881234889094723261227227 (2 : ZMod 79211881234889094723261227227)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (31, 1), (71, 1), (1699, 1), (4421, 1), (14009746766685457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (31, 1), (71, 1), (1699, 1), (4421, 1), (14009746766685457, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_19
      · exact prime_sixtySevenBM_31
      · exact prime_sixtySevenBM_71
      · exact prime_sixtySevenBM_1699
      · exact prime_sixtySevenBM_4421
      · exact prime_sixtySevenBM_14009746766685457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79211881234889094723261227227) ^ 39605940617444547361630613613 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227227) ^ 26403960411629698241087075742 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227227) ^ 4169046380783636564382169854 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227227) ^ 2555221975319003055589071846 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227227) ^ 1115660299082944996102270806 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227227) ^ 46622649343666330031348574 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227227) ^ 17917186436301536919986706 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227227) ^ 5654055177018 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_79211881234889094723261227233 : Nat.Prime 79211881234889094723261227233 := by
  apply lucas_primality 79211881234889094723261227233 (5 : ZMod 79211881234889094723261227233)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (113, 1), (42569981527, 1), (171528855320267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (113, 1), (42569981527, 1), (171528855320267, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_113
      · exact prime_sixtySevenBM_42569981527
      · exact prime_sixtySevenBM_171528855320267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 79211881234889094723261227233) ^ 39605940617444547361630613616 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 79211881234889094723261227233) ^ 26403960411629698241087075744 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 79211881234889094723261227233) ^ 700990099423797298435940064 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 79211881234889094723261227233) ^ 1860745022514256416 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (5 : ZMod 79211881234889094723261227233) ^ 461799159604896 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_79211881234889094723261227237 : Nat.Prime 79211881234889094723261227237 := by
  apply lucas_primality 79211881234889094723261227237 (2 : ZMod 79211881234889094723261227237)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (977, 1), (1723, 1), (11763877546139427185579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (977, 1), (1723, 1), (11763877546139427185579, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_977
      · exact prime_sixtySevenBM_1723
      · exact prime_sixtySevenBM_11763877546139427185579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79211881234889094723261227237) ^ 39605940617444547361630613618 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227237) ^ 81076644047992932163010468 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227237) ^ 45973233450312881441242732 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (2 : ZMod 79211881234889094723261227237) ^ 6733484 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_79211881234889094723261227279 : Nat.Prime 79211881234889094723261227279 := by
  apply lucas_primality 79211881234889094723261227279 (7 : ZMod 79211881234889094723261227279)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19963, 1), (89597, 1), (22143234377352663049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19963, 1), (89597, 1), (22143234377352663049, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_19963
      · exact prime_sixtySevenBM_89597
      · exact prime_sixtySevenBM_22143234377352663049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 79211881234889094723261227279) ^ 39605940617444547361630613639 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 79211881234889094723261227279) ^ 3967934741015333102402506 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 79211881234889094723261227279) ^ 884090775750182424894374 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (7 : ZMod 79211881234889094723261227279) ^ 3577249822 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem prime_sixtySevenBM_79211881234889094723261227281 : Nat.Prime 79211881234889094723261227281 := by
  apply lucas_primality 79211881234889094723261227281 (13 : ZMod 79211881234889094723261227281)
  · rw [← sixtySevenBMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (59, 1), (60264137621, 1), (30941892531091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (59, 1), (60264137621, 1), (30941892531091, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySevenBM_2
      · exact prime_sixtySevenBM_3
      · exact prime_sixtySevenBM_5
      · exact prime_sixtySevenBM_59
      · exact prime_sixtySevenBM_60264137621
      · exact prime_sixtySevenBM_30941892531091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 79211881234889094723261227281) ^ 39605940617444547361630613640 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 79211881234889094723261227281) ^ 26403960411629698241087075760 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 79211881234889094723261227281) ^ 15842376246977818944652245456 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 79211881234889094723261227281) ^ 1342574258218459232597647920 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 79211881234889094723261227281) ^ 1314411594720745680 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide
    · change (13 : ZMod 79211881234889094723261227281) ^ 2560020566140080 ≠ 1
      rw [← sixtySevenBMFastPow_eq_pow]
      decide

private theorem phi_sixtySevenBM_79211881234889094723261227200 : Nat.totient 79211881234889094723261227200 = 27125272686750187277960478720 := by
  rw [← show ((([(2, 6), (5, 2), (7, 1), (1459, 1), (1889, 1), (258403, 1), (9930874732277, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_7, prime_sixtySevenBM_1459, prime_sixtySevenBM_1889, prime_sixtySevenBM_258403, prime_sixtySevenBM_9930874732277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227201 : Nat.totient 79211881234889094723261227201 = 74076301357356035332315210752 := by
  rw [← show ((([(17, 1), (269, 1), (509, 1), (1399, 1), (24325043715992375407, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_17, prime_sixtySevenBM_269, prime_sixtySevenBM_509, prime_sixtySevenBM_1399, prime_sixtySevenBM_24325043715992375407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227202 : Nat.totient 79211881234889094723261227202 = 25493479018125225887946142032 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (455240696752236176570466823, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_29, prime_sixtySevenBM_455240696752236176570466823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227203 : Nat.totient 79211881234889094723261227203 = 79211881234818320611801880808 := by
  rw [← show ((([(1119238833199, 1), (70772992220513197, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_1119238833199, prime_sixtySevenBM_70772992220513197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227204 : Nat.totient 79211881234889094723261227204 = 39328073387400505901336035200 := by
  rw [← show ((([(2, 2), (173, 1), (821, 1), (40591, 1), (3434878070737578767, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_173, prime_sixtySevenBM_821, prime_sixtySevenBM_40591, prime_sixtySevenBM_3434878070737578767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227205 : Nat.totient 79211881234889094723261227205 = 37301113303921018518512282880 := by
  rw [← show ((([(3, 1), (5, 1), (13, 2), (23, 1), (1358577844694093040446981, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_5, prime_sixtySevenBM_13, prime_sixtySevenBM_23, prime_sixtySevenBM_1358577844694093040446981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227206 : Nat.totient 79211881234889094723261227206 = 35994290421011837163386368000 := by
  rw [← show ((([(2, 1), (11, 1), (5741, 1), (7877, 1), (134129, 1), (593603656928441, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_11, prime_sixtySevenBM_5741, prime_sixtySevenBM_7877, prime_sixtySevenBM_134129, prime_sixtySevenBM_593603656928441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227207 : Nat.totient 79211881234889094723261227207 = 62332310142643727858247475200 := by
  rw [← show ((([(7, 2), (19, 1), (41, 1), (149, 1), (542281, 1), (25683022561935593, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_7, prime_sixtySevenBM_19, prime_sixtySevenBM_41, prime_sixtySevenBM_149, prime_sixtySevenBM_542281, prime_sixtySevenBM_25683022561935593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227208 : Nat.totient 79211881234889094723261227208 = 26403932943593838618191693568 := by
  rw [← show ((([(2, 3), (3, 4), (961487, 1), (4854459817, 1), (26189728399, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_961487, prime_sixtySevenBM_4854459817, prime_sixtySevenBM_26189728399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227209 : Nat.totient 79211881234889094723261227209 = 79211788785450028218556633104 := by
  rw [← show ((([(856813, 1), (92449439066504703737293, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_856813, prime_sixtySevenBM_92449439066504703737293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227210 : Nat.totient 79211881234889094723261227210 = 30943999111481786605879296000 := by
  rw [← show ((([(2, 1), (5, 1), (43, 1), (13421, 1), (31319, 1), (56401, 1), (576049, 1), (13489097, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_43, prime_sixtySevenBM_13421, prime_sixtySevenBM_31319, prime_sixtySevenBM_56401, prime_sixtySevenBM_576049, prime_sixtySevenBM_13489097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227211 : Nat.totient 79211881234889094723261227211 = 52807920734683533027576886272 := by
  rw [← show ((([(3, 1), (596188609, 1), (44287931726702443993, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_596188609, prime_sixtySevenBM_44287931726702443993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227212 : Nat.totient 79211881234889094723261227212 = 38530156272498566983477195200 := by
  rw [← show ((([(2, 2), (37, 1), (7211, 1), (4043999, 1), (18353634431779771, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_37, prime_sixtySevenBM_7211, prime_sixtySevenBM_4043999, prime_sixtySevenBM_18353634431779771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227213 : Nat.totient 79211881234889094723261227213 = 79005783683839580951107234048 := by
  rw [← show ((([(449, 1), (2663, 1), (66248007409036892366699, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_449, prime_sixtySevenBM_2663, prime_sixtySevenBM_66248007409036892366699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227214 : Nat.totient 79211881234889094723261227214 = 22631966067111169920931779192 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1885997172259264160077648267, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_7, prime_sixtySevenBM_1885997172259264160077648267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227215 : Nat.totient 79211881234889094723261227215 = 63369504987911275778608981768 := by
  rw [← show ((([(5, 1), (15842376246977818944652245443, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_5, prime_sixtySevenBM_15842376246977818944652245443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227216 : Nat.totient 79211881234889094723261227216 = 39605940617444547361630613600 := by
  rw [← show ((([(2, 4), (4950742577180568420203826701, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_4950742577180568420203826701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227217 : Nat.totient 79211881234889094723261227217 = 48007200748417633165612864920 := by
  rw [← show ((([(3, 2), (11, 1), (800120012473627219426881083, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_11, prime_sixtySevenBM_800120012473627219426881083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227218 : Nat.totient 79211881234889094723261227218 = 34298270095066060566846504960 := by
  rw [← show ((([(2, 1), (13, 1), (17, 1), (313, 1), (59281, 1), (329038277, 1), (29353627409, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_13, prime_sixtySevenBM_17, prime_sixtySevenBM_313, prime_sixtySevenBM_59281, prime_sixtySevenBM_329038277, prime_sixtySevenBM_29353627409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227219 : Nat.totient 79211881234889094723261227219 = 79189611940192752554376415896 := by
  rw [← show ((([(3557, 1), (22269294696342168884807767, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3557, prime_sixtySevenBM_22269294696342168884807767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227220 : Nat.totient 79211881234889094723261227220 = 21118945543040321275590928000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (5051, 1), (517511, 1), (505059010268331767, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_5, prime_sixtySevenBM_5051, prime_sixtySevenBM_517511, prime_sixtySevenBM_505059010268331767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227221 : Nat.totient 79211881234889094723261227221 = 66161422488963073113886500864 := by
  rw [← show ((([(7, 1), (59, 1), (227, 1), (233, 1), (15739, 1), (249989, 1), (921638191597, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_7, prime_sixtySevenBM_59, prime_sixtySevenBM_227, prime_sixtySevenBM_233, prime_sixtySevenBM_15739, prime_sixtySevenBM_249989, prime_sixtySevenBM_921638191597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227222 : Nat.totient 79211881234889094723261227222 = 39592361414911196164775816160 := by
  rw [← show ((([(2, 1), (2917, 1), (25144043, 1), (539993823243244781, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_2917, prime_sixtySevenBM_25144043, prime_sixtySevenBM_539993823243244781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227223 : Nat.totient 79211881234889094723261227223 = 52758560559648278698083705600 := by
  rw [← show ((([(3, 1), (1117, 1), (25321, 1), (1811625971, 1), (515307553603, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_1117, prime_sixtySevenBM_25321, prime_sixtySevenBM_1811625971, prime_sixtySevenBM_515307553603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227224 : Nat.totient 79211881234889094723261227224 = 39221381555084188647977520000 := by
  rw [← show ((([(2, 3), (103, 1), (1109891, 1), (1384024211, 1), (62580510101, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_103, prime_sixtySevenBM_1109891, prime_sixtySevenBM_1384024211, prime_sixtySevenBM_62580510101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227225 : Nat.totient 79211881234889094723261227225 = 62716211121641332796759416320 := by
  rw [← show ((([(5, 2), (97, 1), (151160796119, 1), (216092360793223, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_5, prime_sixtySevenBM_97, prime_sixtySevenBM_151160796119, prime_sixtySevenBM_216092360793223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227226 : Nat.totient 79211881234889094723261227226 = 23846974688656051444931328000 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (31, 1), (71, 1), (1699, 1), (4421, 1), (14009746766685457, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_19, prime_sixtySevenBM_31, prime_sixtySevenBM_71, prime_sixtySevenBM_1699, prime_sixtySevenBM_4421, prime_sixtySevenBM_14009746766685457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227227 : Nat.totient 79211881234889094723261227227 = 79211881234889094723261227226 := by
  rw [← show ((([(79211881234889094723261227227, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_79211881234889094723261227227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227228 : Nat.totient 79211881234889094723261227228 = 29423798962670254842949582080 := by
  rw [← show ((([(2, 2), (7, 1), (11, 1), (23, 1), (307, 1), (51673397, 1), (704865714888523, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_7, prime_sixtySevenBM_11, prime_sixtySevenBM_23, prime_sixtySevenBM_307, prime_sixtySevenBM_51673397, prime_sixtySevenBM_704865714888523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227229 : Nat.totient 79211881234889094723261227229 = 52806589531688765147016098688 := by
  rw [← show ((([(3, 1), (39667, 1), (4964949053, 1), (134067935053193, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_39667, prime_sixtySevenBM_4964949053, prime_sixtySevenBM_134067935053193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227230 : Nat.totient 79211881234889094723261227230 = 31684167665740232991691417344 := by
  rw [← show ((([(2, 1), (5, 1), (80167, 1), (167117, 1), (591253963479944057, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_80167, prime_sixtySevenBM_167117, prime_sixtySevenBM_591253963479944057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227231 : Nat.totient 79211881234889094723261227231 = 70220898771027995185715520000 := by
  rw [← show ((([(13, 1), (29, 1), (199, 1), (3251, 1), (1153871, 1), (281463233802757, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_13, prime_sixtySevenBM_29, prime_sixtySevenBM_199, prime_sixtySevenBM_3251, prime_sixtySevenBM_1153871, prime_sixtySevenBM_281463233802757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227232 : Nat.totient 79211881234889094723261227232 = 26170297044540187153326802944 := by
  rw [← show ((([(2, 5), (3, 1), (113, 1), (42569981527, 1), (171528855320267, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_113, prime_sixtySevenBM_42569981527, prime_sixtySevenBM_171528855320267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227233 : Nat.totient 79211881234889094723261227233 = 79211881234889094723261227232 := by
  rw [← show ((([(79211881234889094723261227233, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_79211881234889094723261227233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227234 : Nat.totient 79211881234889094723261227234 = 39604010792672713298853679920 := by
  rw [← show ((([(2, 1), (20693, 1), (2499139, 1), (765854841786616271, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_20693, prime_sixtySevenBM_2499139, prime_sixtySevenBM_765854841786616271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227235 : Nat.totient 79211881234889094723261227235 = 34080825037638540412632268800 := by
  rw [← show ((([(3, 3), (5, 1), (7, 1), (17, 1), (163351, 1), (763493, 1), (39535090806833, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_5, prime_sixtySevenBM_7, prime_sixtySevenBM_17, prime_sixtySevenBM_163351, prime_sixtySevenBM_763493, prime_sixtySevenBM_39535090806833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227236 : Nat.totient 79211881234889094723261227236 = 39542439206450486733679496832 := by
  rw [← show ((([(2, 2), (977, 1), (1723, 1), (11763877546139427185579, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_977, prime_sixtySevenBM_1723, prime_sixtySevenBM_11763877546139427185579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227237 : Nat.totient 79211881234889094723261227237 = 79211881234889094723261227236 := by
  rw [← show ((([(79211881234889094723261227237, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_79211881234889094723261227237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227238 : Nat.totient 79211881234889094723261227238 = 26340982124485121748554876928 := by
  rw [← show ((([(2, 1), (3, 1), (433, 1), (13177, 1), (2313846981577503582953, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_433, prime_sixtySevenBM_13177, prime_sixtySevenBM_2313846981577503582953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227239 : Nat.totient 79211881234889094723261227239 = 71783593857856442849935586400 := by
  rw [← show ((([(11, 1), (317, 1), (1636867, 1), (13877939409950316691, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_11, prime_sixtySevenBM_317, prime_sixtySevenBM_1636867, prime_sixtySevenBM_13877939409950316691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227240 : Nat.totient 79211881234889094723261227240 = 31086926975201757929128933632 := by
  rw [← show ((([(2, 3), (5, 1), (53, 1), (37364094922117497510972277, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_53, prime_sixtySevenBM_37364094922117497510972277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227241 : Nat.totient 79211881234889094723261227241 = 52045216136130599274846412800 := by
  rw [← show ((([(3, 1), (101, 1), (229, 1), (4513, 1), (894134869, 1), (282907103119, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_101, prime_sixtySevenBM_229, prime_sixtySevenBM_4513, prime_sixtySevenBM_894134869, prime_sixtySevenBM_282907103119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227242 : Nat.totient 79211881234889094723261227242 = 33222357345905176856723343360 := by
  rw [← show ((([(2, 1), (7, 1), (47, 1), (10159, 1), (1413781, 1), (46119959, 1), (181736609, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_7, prime_sixtySevenBM_47, prime_sixtySevenBM_10159, prime_sixtySevenBM_1413781, prime_sixtySevenBM_46119959, prime_sixtySevenBM_181736609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227243 : Nat.totient 79211881234889094723261227243 = 78126778750472635465288895040 := by
  rw [← show ((([(73, 1), (9527339, 1), (4437147431, 1), (25667997599, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_73, prime_sixtySevenBM_9527339, prime_sixtySevenBM_4437147431, prime_sixtySevenBM_25667997599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227244 : Nat.totient 79211881234889094723261227244 = 24372869767150647500134210944 := by
  rw [← show ((([(2, 2), (3, 2), (13, 1), (1857967, 1), (6680027, 1), (13637295799187, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_13, prime_sixtySevenBM_1857967, prime_sixtySevenBM_6680027, prime_sixtySevenBM_13637295799187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227245 : Nat.totient 79211881234889094723261227245 = 59050099557328885108626139200 := by
  rw [← show ((([(5, 1), (19, 1), (61, 1), (13669004527159464145515311, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_5, prime_sixtySevenBM_19, prime_sixtySevenBM_61, prime_sixtySevenBM_13669004527159464145515311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227246 : Nat.totient 79211881234889094723261227246 = 39592442176724321925290490240 := by
  rw [← show ((([(2, 1), (2957, 1), (379693, 1), (193092043, 1), (182688848861, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_2957, prime_sixtySevenBM_379693, prime_sixtySevenBM_193092043, prime_sixtySevenBM_182688848861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227247 : Nat.totient 79211881234889094723261227247 = 52419555683230508356452967392 := by
  rw [← show ((([(3, 1), (139, 1), (6203, 1), (30623335438328980107197, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_139, prime_sixtySevenBM_6203, prime_sixtySevenBM_30623335438328980107197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227248 : Nat.totient 79211881234889094723261227248 = 38639942065736654850886003200 := by
  rw [← show ((([(2, 4), (41, 1), (616204461781, 1), (195957391490843, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_41, prime_sixtySevenBM_616204461781, prime_sixtySevenBM_195957391490843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227249 : Nat.totient 79211881234889094723261227249 = 66060868281087095476960536000 := by
  rw [← show ((([(7, 1), (37, 1), (11703511, 1), (26132105082422367101, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_7, prime_sixtySevenBM_37, prime_sixtySevenBM_11703511, prime_sixtySevenBM_26132105082422367101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227250 : Nat.totient 79211881234889094723261227250 = 19004333472248296437111072000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 3), (11, 1), (107, 1), (997, 1), (90003094795447338587, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_5, prime_sixtySevenBM_11, prime_sixtySevenBM_107, prime_sixtySevenBM_997, prime_sixtySevenBM_90003094795447338587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227251 : Nat.totient 79211881234889094723261227251 = 75767886398380799329751742720 := by
  rw [← show ((([(23, 1), (362939851361, 1), (9489161422711717, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_23, prime_sixtySevenBM_362939851361, prime_sixtySevenBM_9489161422711717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227252 : Nat.totient 79211881234889094723261227252 = 37276179404653691634475871616 := by
  rw [← show ((([(2, 2), (17, 1), (1164880606395427863577370989, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_17, prime_sixtySevenBM_1164880606395427863577370989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227253 : Nat.totient 79211881234889094723261227253 = 51568156477031671039006080000 := by
  rw [← show ((([(3, 2), (43, 1), (4751, 1), (63337, 1), (22066757, 1), (30824662541, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_43, prime_sixtySevenBM_4751, prime_sixtySevenBM_63337, prime_sixtySevenBM_22066757, prime_sixtySevenBM_30824662541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227254 : Nat.totient 79211881234889094723261227254 = 39099818499086109145257722664 := by
  rw [← show ((([(2, 1), (79, 1), (8179, 1), (61296126723802617945047, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_79, prime_sixtySevenBM_8179, prime_sixtySevenBM_61296126723802617945047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227255 : Nat.totient 79211881234889094723261227255 = 62906931600032967617751713280 := by
  rw [← show ((([(5, 1), (137, 1), (2826443, 1), (40912830304610994361, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_5, prime_sixtySevenBM_137, prime_sixtySevenBM_2826443, prime_sixtySevenBM_40912830304610994361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227256 : Nat.totient 79211881234889094723261227256 = 22591332365836991326639523328 := by
  rw [← show ((([(2, 3), (3, 1), (7, 3), (557, 1), (12514013, 1), (1380489694445963, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_7, prime_sixtySevenBM_557, prime_sixtySevenBM_12514013, prime_sixtySevenBM_1380489694445963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227257 : Nat.totient 79211881234889094723261227257 = 70697318234810786884920384000 := by
  rw [← show ((([(13, 1), (31, 1), (1129, 1), (304428014791, 1), (571882390621, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_13, prime_sixtySevenBM_31, prime_sixtySevenBM_1129, prime_sixtySevenBM_304428014791, prime_sixtySevenBM_571882390621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227258 : Nat.totient 79211881234889094723261227258 = 39605264658418641131073507840 := by
  rw [← show ((([(2, 1), (60293, 1), (2077073, 1), (316258114971521161, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_60293, prime_sixtySevenBM_2077073, prime_sixtySevenBM_316258114971521161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227259 : Nat.totient 79211881234889094723261227259 = 51289087549093018711671138048 := by
  rw [← show ((([(3, 1), (67, 1), (89, 1), (359, 1), (17747, 1), (695000097794080447, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_67, prime_sixtySevenBM_89, prime_sixtySevenBM_359, prime_sixtySevenBM_17747, prime_sixtySevenBM_695000097794080447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227260 : Nat.totient 79211881234889094723261227260 = 30583813372127412053914311936 := by
  rw [← show ((([(2, 2), (5, 1), (29, 1), (5107, 1), (12899, 1), (2073196340019388679, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_29, prime_sixtySevenBM_5107, prime_sixtySevenBM_12899, prime_sixtySevenBM_2073196340019388679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227261 : Nat.totient 79211881234889094723261227261 = 72008319446329016297344374720 := by
  rw [← show ((([(11, 2), (29017, 1), (22560693613031373379373, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_11, prime_sixtySevenBM_29017, prime_sixtySevenBM_22560693613031373379373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227262 : Nat.totient 79211881234889094723261227262 = 26403960411629698241087075736 := by
  rw [← show ((([(2, 1), (3, 3), (1466886689534983235615948653, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_1466886689534983235615948653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227263 : Nat.totient 79211881234889094723261227263 = 67895898200917617307045743360 := by
  rw [← show ((([(7, 1), (163253882521, 1), (69315246037716529, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_7, prime_sixtySevenBM_163253882521, prime_sixtySevenBM_69315246037716529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227264 : Nat.totient 79211881234889094723261227264 = 37501803513081452169304731648 := by
  rw [← show ((([(2, 8), (19, 1), (1913, 1), (8512983494477825577427, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_19, prime_sixtySevenBM_1913, prime_sixtySevenBM_8512983494477825577427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227265 : Nat.totient 79211881234889094723261227265 = 42173376670601029239747379200 := by
  rw [← show ((([(3, 1), (5, 1), (769, 1), (2341, 1), (91962259, 1), (31897870031441, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_5, prime_sixtySevenBM_769, prime_sixtySevenBM_2341, prime_sixtySevenBM_91962259, prime_sixtySevenBM_31897870031441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227266 : Nat.totient 79211881234889094723261227266 = 39605940614261023833468885828 := by
  rw [← show ((([(2, 1), (12440913479, 1), (3183523515720814327, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_12440913479, prime_sixtySevenBM_3183523515720814327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227267 : Nat.totient 79211881234889094723261227267 = 79211799857148155830982960800 := by
  rw [← show ((([(973421, 1), (26629795691, 1), (3055777873997, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_973421, prime_sixtySevenBM_26629795691, prime_sixtySevenBM_3055777873997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227268 : Nat.totient 79211881234889094723261227268 = 26401068227317201209557419680 := by
  rw [← show ((([(2, 2), (3, 1), (9431, 1), (285463, 1), (2451892985334528763, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_9431, prime_sixtySevenBM_285463, prime_sixtySevenBM_2451892985334528763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227269 : Nat.totient 79211881234889094723261227269 = 74552358809307383268951743296 := by
  rw [← show ((([(17, 1), (4659522425581711454309483957, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_17, prime_sixtySevenBM_4659522425581711454309483957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227270 : Nat.totient 79211881234889094723261227270 = 25069254720427546853160665088 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (13, 1), (387382846693, 1), (224702833587329, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_7, prime_sixtySevenBM_13, prime_sixtySevenBM_387382846693, prime_sixtySevenBM_224702833587329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227271 : Nat.totient 79211881234889094723261227271 = 52171668766092344341294659456 := by
  rw [← show ((([(3, 2), (83, 1), (4330589, 1), (24486276959815701337, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_83, prime_sixtySevenBM_4330589, prime_sixtySevenBM_24486276959815701337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227272 : Nat.totient 79211881234889094723261227272 = 35834758846717413356578425600 := by
  rw [← show ((([(2, 3), (11, 1), (211, 1), (6205830373, 1), (687424963965373, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_11, prime_sixtySevenBM_211, prime_sixtySevenBM_6205830373, prime_sixtySevenBM_687424963965373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227273 : Nat.totient 79211881234889094723261227273 = 79211881234884834689961651840 := by
  rw [← show ((([(18676069223321, 1), (4241357230352113, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_18676069223321, prime_sixtySevenBM_4241357230352113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227274 : Nat.totient 79211881234889094723261227274 = 25211516822272545623546941440 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (941, 1), (1433, 1), (2416656757, 1), (176140999513, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_23, prime_sixtySevenBM_941, prime_sixtySevenBM_1433, prime_sixtySevenBM_2416656757, prime_sixtySevenBM_176140999513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227275 : Nat.totient 79211881234889094723261227275 = 62907891827960364582039552000 := by
  rw [← show ((([(5, 2), (337, 1), (431, 1), (571, 1), (4967, 1), (16057, 1), (479014293097, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_5, prime_sixtySevenBM_337, prime_sixtySevenBM_431, prime_sixtySevenBM_571, prime_sixtySevenBM_4967, prime_sixtySevenBM_16057, prime_sixtySevenBM_479014293097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227276 : Nat.totient 79211881234889094723261227276 = 39569624817853624347097425600 := by
  rw [← show ((([(2, 2), (1621, 1), (3331, 1), (3667521671472734247869, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_1621, prime_sixtySevenBM_3331, prime_sixtySevenBM_3667521671472734247869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227277 : Nat.totient 79211881234889094723261227277 = 45061084917762666746080260096 := by
  rw [← show ((([(3, 1), (7, 1), (349, 1), (617, 1), (1883613437, 1), (9299694073097, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_7, prime_sixtySevenBM_349, prime_sixtySevenBM_617, prime_sixtySevenBM_1883613437, prime_sixtySevenBM_9299694073097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227278 : Nat.totient 79211881234889094723261227278 = 39603514626829398979431112896 := by
  rw [← show ((([(2, 1), (19963, 1), (89597, 1), (22143234377352663049, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_19963, prime_sixtySevenBM_89597, prime_sixtySevenBM_22143234377352663049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227279 : Nat.totient 79211881234889094723261227279 = 79211881234889094723261227278 := by
  rw [← show ((([(79211881234889094723261227279, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_79211881234889094723261227279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227280 : Nat.totient 79211881234889094723261227280 = 20765148526766929447514188800 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (59, 1), (60264137621, 1), (30941892531091, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_5, prime_sixtySevenBM_59, prime_sixtySevenBM_60264137621, prime_sixtySevenBM_30941892531091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227281 : Nat.totient 79211881234889094723261227281 = 79211881234889094723261227280 := by
  rw [← show ((([(79211881234889094723261227281, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_79211881234889094723261227281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227282 : Nat.totient 79211881234889094723261227282 = 39592570388018802728937319440 := by
  rw [← show ((([(2, 1), (2971, 1), (1005287, 1), (13260735532453163933, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_2971, prime_sixtySevenBM_1005287, prime_sixtySevenBM_13260735532453163933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227283 : Nat.totient 79211881234889094723261227283 = 41982005504748176700635335680 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (19, 2), (5223159479, 1), (97924767070033, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_11, prime_sixtySevenBM_13, prime_sixtySevenBM_19, prime_sixtySevenBM_5223159479, prime_sixtySevenBM_97924767070033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227284 : Nat.totient 79211881234889094723261227284 = 33939391513295777630356179936 := by
  rw [← show ((([(2, 2), (7, 1), (3967, 1), (713132280914770920120109, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_7, prime_sixtySevenBM_3967, prime_sixtySevenBM_713132280914770920120109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227285 : Nat.totient 79211881234889094723261227285 = 62788133382517594349447431104 := by
  rw [← show ((([(5, 1), (109, 1), (145342901348420357290387573, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_5, prime_sixtySevenBM_109, prime_sixtySevenBM_145342901348420357290387573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227286 : Nat.totient 79211881234889094723261227286 = 24164115360774599730638979072 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (37, 1), (1609, 1), (40170517, 1), (324731909670713, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_17, prime_sixtySevenBM_37, prime_sixtySevenBM_1609, prime_sixtySevenBM_40170517, prime_sixtySevenBM_324731909670713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227287 : Nat.totient 79211881234889094723261227287 = 79206187794394209290018766720 := by
  rw [← show ((([(13913, 1), (1152268921, 1), (4941009561034919, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_13913, prime_sixtySevenBM_1152268921, prime_sixtySevenBM_4941009561034919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227288 : Nat.totient 79211881234889094723261227288 = 38328290530934365695182480640 := by
  rw [← show ((([(2, 3), (31, 1), (980293, 1), (325823755667821133017, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_31, prime_sixtySevenBM_980293, prime_sixtySevenBM_325823755667821133017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227289 : Nat.totient 79211881234889094723261227289 = 48680702329870826171919728640 := by
  rw [← show ((([(3, 4), (29, 1), (41, 1), (47, 1), (17333, 1), (32609, 1), (30960957157519, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_29, prime_sixtySevenBM_41, prime_sixtySevenBM_47, prime_sixtySevenBM_17333, prime_sixtySevenBM_32609, prime_sixtySevenBM_30960957157519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227290 : Nat.totient 79211881234889094723261227290 = 31637915968484380692220821504 := by
  rw [← show ((([(2, 1), (5, 1), (677, 1), (908533, 1), (12878371604124352769, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_677, prime_sixtySevenBM_908533, prime_sixtySevenBM_12878371604124352769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227291 : Nat.totient 79211881234889094723261227291 = 67738273577370313116979760640 := by
  rw [← show ((([(7, 1), (457, 1), (7481, 1), (3309911888690030779789, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_7, prime_sixtySevenBM_457, prime_sixtySevenBM_7481, prime_sixtySevenBM_3309911888690030779789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227292 : Nat.totient 79211881234889094723261227292 = 26229010418943313731526195200 := by
  rw [← show ((([(2, 2), (3, 1), (151, 1), (304849, 1), (7977043, 1), (17976511895113, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_151, prime_sixtySevenBM_304849, prime_sixtySevenBM_7977043, prime_sixtySevenBM_17976511895113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227293 : Nat.totient 79211881234889094723261227293 = 77717317438004394822822336160 := by
  rw [← show ((([(53, 1), (1494563796884699900438891081, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_53, prime_sixtySevenBM_1494563796884699900438891081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227294 : Nat.totient 79211881234889094723261227294 = 35804234589219156202112051200 := by
  rw [← show ((([(2, 1), (11, 1), (179, 1), (1937153, 1), (10383665573620030271, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_11, prime_sixtySevenBM_179, prime_sixtySevenBM_1937153, prime_sixtySevenBM_10383665573620030271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227295 : Nat.totient 79211881234889094723261227295 = 42246259397756210426427221760 := by
  rw [← show ((([(3, 1), (5, 1), (546841, 1), (7583399519, 1), (1273427027207, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_3, prime_sixtySevenBM_5, prime_sixtySevenBM_546841, prime_sixtySevenBM_7583399519, prime_sixtySevenBM_1273427027207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227296 : Nat.totient 79211881234889094723261227296 = 35707021763852884146371066880 := by
  rw [← show ((([(2, 5), (13, 1), (43, 1), (17077, 1), (259308625426292780171, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_13, prime_sixtySevenBM_43, prime_sixtySevenBM_17077, prime_sixtySevenBM_259308625426292780171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227297 : Nat.totient 79211881234889094723261227297 = 74106782214378514093042260480 := by
  rw [← show ((([(23, 1), (71, 1), (167, 1), (523, 1), (17183, 1), (210499, 1), (153545451497, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_23, prime_sixtySevenBM_71, prime_sixtySevenBM_167, prime_sixtySevenBM_523, prime_sixtySevenBM_17183, prime_sixtySevenBM_210499, prime_sixtySevenBM_153545451497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227298 : Nat.totient 79211881234889094723261227298 = 22631966067099533713182196128 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (1956807057427, 1), (321271185986549, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_3, prime_sixtySevenBM_7, prime_sixtySevenBM_1956807057427, prime_sixtySevenBM_321271185986549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227299 : Nat.totient 79211881234889094723261227299 = 79211881232296259358424167000 := by
  rw [← show ((([(30550293799, 1), (2592835334286766501, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_30550293799, prime_sixtySevenBM_2592835334286766501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySevenBM_79211881234889094723261227300 : Nat.totient 79211881234889094723261227300 = 31684752493955637889304490880 := by
  rw [← show ((([(2, 2), (5, 2), (792118812348890947232612273, 1)] : List FactorBlock).map factorBlockValue).prod) = 79211881234889094723261227300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySevenBM_2, prime_sixtySevenBM_5, prime_sixtySevenBM_792118812348890947232612273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtySevenBM : certifiedKill 1 79211881234889094723261227199 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtySevenBM_79211881234889094723261227200, phi_sixtySevenBM_79211881234889094723261227201, phi_sixtySevenBM_79211881234889094723261227202,
    phi_sixtySevenBM_79211881234889094723261227203, phi_sixtySevenBM_79211881234889094723261227204, phi_sixtySevenBM_79211881234889094723261227205,
    phi_sixtySevenBM_79211881234889094723261227206, phi_sixtySevenBM_79211881234889094723261227207, phi_sixtySevenBM_79211881234889094723261227208,
    phi_sixtySevenBM_79211881234889094723261227209, phi_sixtySevenBM_79211881234889094723261227210, phi_sixtySevenBM_79211881234889094723261227211,
    phi_sixtySevenBM_79211881234889094723261227212, phi_sixtySevenBM_79211881234889094723261227213, phi_sixtySevenBM_79211881234889094723261227214,
    phi_sixtySevenBM_79211881234889094723261227215, phi_sixtySevenBM_79211881234889094723261227216, phi_sixtySevenBM_79211881234889094723261227217,
    phi_sixtySevenBM_79211881234889094723261227218, phi_sixtySevenBM_79211881234889094723261227219, phi_sixtySevenBM_79211881234889094723261227220,
    phi_sixtySevenBM_79211881234889094723261227221, phi_sixtySevenBM_79211881234889094723261227222, phi_sixtySevenBM_79211881234889094723261227223,
    phi_sixtySevenBM_79211881234889094723261227224, phi_sixtySevenBM_79211881234889094723261227225, phi_sixtySevenBM_79211881234889094723261227226,
    phi_sixtySevenBM_79211881234889094723261227227, phi_sixtySevenBM_79211881234889094723261227228, phi_sixtySevenBM_79211881234889094723261227229,
    phi_sixtySevenBM_79211881234889094723261227230, phi_sixtySevenBM_79211881234889094723261227231, phi_sixtySevenBM_79211881234889094723261227232,
    phi_sixtySevenBM_79211881234889094723261227233, phi_sixtySevenBM_79211881234889094723261227234, phi_sixtySevenBM_79211881234889094723261227235,
    phi_sixtySevenBM_79211881234889094723261227236, phi_sixtySevenBM_79211881234889094723261227237, phi_sixtySevenBM_79211881234889094723261227238,
    phi_sixtySevenBM_79211881234889094723261227239, phi_sixtySevenBM_79211881234889094723261227240, phi_sixtySevenBM_79211881234889094723261227241,
    phi_sixtySevenBM_79211881234889094723261227242, phi_sixtySevenBM_79211881234889094723261227243, phi_sixtySevenBM_79211881234889094723261227244,
    phi_sixtySevenBM_79211881234889094723261227245, phi_sixtySevenBM_79211881234889094723261227246, phi_sixtySevenBM_79211881234889094723261227247,
    phi_sixtySevenBM_79211881234889094723261227248, phi_sixtySevenBM_79211881234889094723261227249, phi_sixtySevenBM_79211881234889094723261227250,
    phi_sixtySevenBM_79211881234889094723261227251, phi_sixtySevenBM_79211881234889094723261227252, phi_sixtySevenBM_79211881234889094723261227253,
    phi_sixtySevenBM_79211881234889094723261227254, phi_sixtySevenBM_79211881234889094723261227255, phi_sixtySevenBM_79211881234889094723261227256,
    phi_sixtySevenBM_79211881234889094723261227257, phi_sixtySevenBM_79211881234889094723261227258, phi_sixtySevenBM_79211881234889094723261227259,
    phi_sixtySevenBM_79211881234889094723261227260, phi_sixtySevenBM_79211881234889094723261227261, phi_sixtySevenBM_79211881234889094723261227262,
    phi_sixtySevenBM_79211881234889094723261227263, phi_sixtySevenBM_79211881234889094723261227264, phi_sixtySevenBM_79211881234889094723261227265,
    phi_sixtySevenBM_79211881234889094723261227266, phi_sixtySevenBM_79211881234889094723261227267, phi_sixtySevenBM_79211881234889094723261227268,
    phi_sixtySevenBM_79211881234889094723261227269, phi_sixtySevenBM_79211881234889094723261227270, phi_sixtySevenBM_79211881234889094723261227271,
    phi_sixtySevenBM_79211881234889094723261227272, phi_sixtySevenBM_79211881234889094723261227273, phi_sixtySevenBM_79211881234889094723261227274,
    phi_sixtySevenBM_79211881234889094723261227275, phi_sixtySevenBM_79211881234889094723261227276, phi_sixtySevenBM_79211881234889094723261227277,
    phi_sixtySevenBM_79211881234889094723261227278, phi_sixtySevenBM_79211881234889094723261227279, phi_sixtySevenBM_79211881234889094723261227280,
    phi_sixtySevenBM_79211881234889094723261227281, phi_sixtySevenBM_79211881234889094723261227282, phi_sixtySevenBM_79211881234889094723261227283,
    phi_sixtySevenBM_79211881234889094723261227284, phi_sixtySevenBM_79211881234889094723261227285, phi_sixtySevenBM_79211881234889094723261227286,
    phi_sixtySevenBM_79211881234889094723261227287, phi_sixtySevenBM_79211881234889094723261227288, phi_sixtySevenBM_79211881234889094723261227289,
    phi_sixtySevenBM_79211881234889094723261227290, phi_sixtySevenBM_79211881234889094723261227291, phi_sixtySevenBM_79211881234889094723261227292,
    phi_sixtySevenBM_79211881234889094723261227293, phi_sixtySevenBM_79211881234889094723261227294, phi_sixtySevenBM_79211881234889094723261227295,
    phi_sixtySevenBM_79211881234889094723261227296, phi_sixtySevenBM_79211881234889094723261227297, phi_sixtySevenBM_79211881234889094723261227298,
    phi_sixtySevenBM_79211881234889094723261227299, phi_sixtySevenBM_79211881234889094723261227300]

end TotientTailPeriodKiller
end Erdos249257
