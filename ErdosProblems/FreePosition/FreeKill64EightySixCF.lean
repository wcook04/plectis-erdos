import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightySixCFFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightySixCFFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightySixCFFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightySixCFFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightySixCFFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightySixCFFastPow a n * eightySixCFFastPow a n * a else eightySixCFFastPow a n * eightySixCFFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightySixCF_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightySixCF_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightySixCF_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightySixCF_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightySixCF_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightySixCF_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightySixCF_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightySixCF_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightySixCF_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightySixCF_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightySixCF_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightySixCF_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightySixCF_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightySixCF_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightySixCF_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightySixCF_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightySixCF_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightySixCF_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightySixCF_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightySixCF_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightySixCF_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightySixCF_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightySixCF_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightySixCF_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightySixCF_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightySixCF_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightySixCF_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightySixCF_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightySixCF_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightySixCF_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightySixCF_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightySixCF_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightySixCF_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightySixCF_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightySixCF_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightySixCF_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightySixCF_157 : Nat.Prime 157 := by norm_num

private theorem prime_eightySixCF_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightySixCF_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightySixCF_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightySixCF_179 : Nat.Prime 179 := by norm_num

private theorem prime_eightySixCF_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightySixCF_191 : Nat.Prime 191 := by norm_num

private theorem prime_eightySixCF_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightySixCF_197 : Nat.Prime 197 := by norm_num

private theorem prime_eightySixCF_199 : Nat.Prime 199 := by norm_num

private theorem prime_eightySixCF_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightySixCF_223 : Nat.Prime 223 := by norm_num

private theorem prime_eightySixCF_229 : Nat.Prime 229 := by norm_num

private theorem prime_eightySixCF_233 : Nat.Prime 233 := by norm_num

private theorem prime_eightySixCF_239 : Nat.Prime 239 := by norm_num

private theorem prime_eightySixCF_241 : Nat.Prime 241 := by norm_num

private theorem prime_eightySixCF_251 : Nat.Prime 251 := by norm_num

private theorem prime_eightySixCF_263 : Nat.Prime 263 := by norm_num

private theorem prime_eightySixCF_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightySixCF_271 : Nat.Prime 271 := by norm_num

private theorem prime_eightySixCF_277 : Nat.Prime 277 := by norm_num

private theorem prime_eightySixCF_281 : Nat.Prime 281 := by norm_num

private theorem prime_eightySixCF_283 : Nat.Prime 283 := by norm_num

private theorem prime_eightySixCF_307 : Nat.Prime 307 := by norm_num

private theorem prime_eightySixCF_313 : Nat.Prime 313 := by norm_num

private theorem prime_eightySixCF_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightySixCF_347 : Nat.Prime 347 := by norm_num

private theorem prime_eightySixCF_349 : Nat.Prime 349 := by norm_num

private theorem prime_eightySixCF_359 : Nat.Prime 359 := by norm_num

private theorem prime_eightySixCF_367 : Nat.Prime 367 := by norm_num

private theorem prime_eightySixCF_389 : Nat.Prime 389 := by norm_num

private theorem prime_eightySixCF_397 : Nat.Prime 397 := by norm_num

private theorem prime_eightySixCF_431 : Nat.Prime 431 := by norm_num

private theorem prime_eightySixCF_433 : Nat.Prime 433 := by norm_num

private theorem prime_eightySixCF_439 : Nat.Prime 439 := by norm_num

private theorem prime_eightySixCF_443 : Nat.Prime 443 := by norm_num

private theorem prime_eightySixCF_449 : Nat.Prime 449 := by norm_num

private theorem prime_eightySixCF_457 : Nat.Prime 457 := by norm_num

private theorem prime_eightySixCF_461 : Nat.Prime 461 := by norm_num

private theorem prime_eightySixCF_463 : Nat.Prime 463 := by norm_num

private theorem prime_eightySixCF_479 : Nat.Prime 479 := by norm_num

private theorem prime_eightySixCF_487 : Nat.Prime 487 := by norm_num

private theorem prime_eightySixCF_499 : Nat.Prime 499 := by norm_num

private theorem prime_eightySixCF_503 : Nat.Prime 503 := by norm_num

private theorem prime_eightySixCF_509 : Nat.Prime 509 := by norm_num

private theorem prime_eightySixCF_523 : Nat.Prime 523 := by norm_num

private theorem prime_eightySixCF_557 : Nat.Prime 557 := by norm_num

private theorem prime_eightySixCF_571 : Nat.Prime 571 := by norm_num

private theorem prime_eightySixCF_577 : Nat.Prime 577 := by norm_num

private theorem prime_eightySixCF_587 : Nat.Prime 587 := by norm_num

private theorem prime_eightySixCF_601 : Nat.Prime 601 := by norm_num

private theorem prime_eightySixCF_607 : Nat.Prime 607 := by norm_num

private theorem prime_eightySixCF_641 : Nat.Prime 641 := by norm_num

private theorem prime_eightySixCF_653 : Nat.Prime 653 := by norm_num

private theorem prime_eightySixCF_659 : Nat.Prime 659 := by norm_num

private theorem prime_eightySixCF_683 : Nat.Prime 683 := by norm_num

private theorem prime_eightySixCF_691 : Nat.Prime 691 := by norm_num

private theorem prime_eightySixCF_719 : Nat.Prime 719 := by norm_num

private theorem prime_eightySixCF_727 : Nat.Prime 727 := by norm_num

private theorem prime_eightySixCF_743 : Nat.Prime 743 := by norm_num

private theorem prime_eightySixCF_751 : Nat.Prime 751 := by norm_num

private theorem prime_eightySixCF_769 : Nat.Prime 769 := by norm_num

private theorem prime_eightySixCF_773 : Nat.Prime 773 := by norm_num

private theorem prime_eightySixCF_787 : Nat.Prime 787 := by norm_num

private theorem prime_eightySixCF_809 : Nat.Prime 809 := by norm_num

private theorem prime_eightySixCF_823 : Nat.Prime 823 := by norm_num

private theorem prime_eightySixCF_827 : Nat.Prime 827 := by norm_num

private theorem prime_eightySixCF_839 : Nat.Prime 839 := by norm_num

private theorem prime_eightySixCF_853 : Nat.Prime 853 := by norm_num

private theorem prime_eightySixCF_859 : Nat.Prime 859 := by norm_num

private theorem prime_eightySixCF_863 : Nat.Prime 863 := by norm_num

private theorem prime_eightySixCF_883 : Nat.Prime 883 := by norm_num

private theorem prime_eightySixCF_907 : Nat.Prime 907 := by norm_num

private theorem prime_eightySixCF_911 : Nat.Prime 911 := by norm_num

private theorem prime_eightySixCF_937 : Nat.Prime 937 := by norm_num

private theorem prime_eightySixCF_947 : Nat.Prime 947 := by norm_num

private theorem prime_eightySixCF_953 : Nat.Prime 953 := by norm_num

private theorem prime_eightySixCF_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_eightySixCF_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_eightySixCF_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_eightySixCF_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_eightySixCF_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_eightySixCF_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_eightySixCF_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_eightySixCF_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_eightySixCF_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_eightySixCF_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_eightySixCF_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_eightySixCF_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_eightySixCF_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_eightySixCF_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_eightySixCF_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_eightySixCF_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_eightySixCF_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_eightySixCF_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_eightySixCF_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_eightySixCF_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_eightySixCF_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_eightySixCF_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_eightySixCF_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_eightySixCF_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_eightySixCF_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_eightySixCF_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_eightySixCF_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_eightySixCF_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_eightySixCF_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_eightySixCF_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_eightySixCF_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_eightySixCF_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_eightySixCF_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_eightySixCF_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_eightySixCF_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_eightySixCF_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_eightySixCF_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_eightySixCF_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_eightySixCF_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_eightySixCF_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_eightySixCF_3389 : Nat.Prime 3389 := by norm_num

private theorem prime_eightySixCF_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_eightySixCF_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_eightySixCF_3947 : Nat.Prime 3947 := by norm_num

private theorem prime_eightySixCF_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_eightySixCF_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_eightySixCF_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_eightySixCF_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_eightySixCF_4339 : Nat.Prime 4339 := by norm_num

private theorem prime_eightySixCF_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_eightySixCF_4507 : Nat.Prime 4507 := by norm_num

private theorem prime_eightySixCF_4517 : Nat.Prime 4517 := by norm_num

private theorem prime_eightySixCF_4549 : Nat.Prime 4549 := by norm_num

private theorem prime_eightySixCF_4679 : Nat.Prime 4679 := by norm_num

private theorem prime_eightySixCF_4817 : Nat.Prime 4817 := by norm_num

private theorem prime_eightySixCF_5039 : Nat.Prime 5039 := by norm_num

private theorem prime_eightySixCF_5171 : Nat.Prime 5171 := by norm_num

private theorem prime_eightySixCF_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_eightySixCF_5483 : Nat.Prime 5483 := by norm_num

private theorem prime_eightySixCF_5623 : Nat.Prime 5623 := by norm_num

private theorem prime_eightySixCF_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_eightySixCF_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_eightySixCF_6163 : Nat.Prime 6163 := by norm_num

private theorem prime_eightySixCF_6173 : Nat.Prime 6173 := by norm_num

private theorem prime_eightySixCF_6329 : Nat.Prime 6329 := by norm_num

private theorem prime_eightySixCF_6379 : Nat.Prime 6379 := by norm_num

private theorem prime_eightySixCF_6421 : Nat.Prime 6421 := by norm_num

private theorem prime_eightySixCF_6449 : Nat.Prime 6449 := by norm_num

private theorem prime_eightySixCF_6491 : Nat.Prime 6491 := by norm_num

private theorem prime_eightySixCF_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_eightySixCF_6719 : Nat.Prime 6719 := by norm_num

private theorem prime_eightySixCF_6763 : Nat.Prime 6763 := by norm_num

private theorem prime_eightySixCF_6779 : Nat.Prime 6779 := by norm_num

private theorem prime_eightySixCF_6991 : Nat.Prime 6991 := by norm_num

private theorem prime_eightySixCF_7187 : Nat.Prime 7187 := by norm_num

private theorem prime_eightySixCF_7507 : Nat.Prime 7507 := by norm_num

private theorem prime_eightySixCF_7517 : Nat.Prime 7517 := by norm_num

private theorem prime_eightySixCF_7877 : Nat.Prime 7877 := by norm_num

private theorem prime_eightySixCF_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_eightySixCF_8243 : Nat.Prime 8243 := by norm_num

private theorem prime_eightySixCF_8431 : Nat.Prime 8431 := by norm_num

private theorem prime_eightySixCF_8623 : Nat.Prime 8623 := by norm_num

private theorem prime_eightySixCF_8887 : Nat.Prime 8887 := by norm_num

private theorem prime_eightySixCF_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_eightySixCF_9437 : Nat.Prime 9437 := by norm_num

private theorem prime_eightySixCF_9679 : Nat.Prime 9679 := by norm_num

private theorem prime_eightySixCF_9931 : Nat.Prime 9931 := by norm_num

private theorem prime_eightySixCF_10099 : Nat.Prime 10099 := by norm_num

private theorem prime_eightySixCF_10253 : Nat.Prime 10253 := by norm_num

private theorem prime_eightySixCF_10457 : Nat.Prime 10457 := by norm_num

private theorem prime_eightySixCF_10513 : Nat.Prime 10513 := by norm_num

private theorem prime_eightySixCF_10531 : Nat.Prime 10531 := by norm_num

private theorem prime_eightySixCF_11093 : Nat.Prime 11093 := by norm_num

private theorem prime_eightySixCF_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_eightySixCF_11821 : Nat.Prime 11821 := by norm_num

private theorem prime_eightySixCF_11969 : Nat.Prime 11969 := by norm_num

private theorem prime_eightySixCF_11981 : Nat.Prime 11981 := by norm_num

private theorem prime_eightySixCF_12739 : Nat.Prime 12739 := by norm_num

private theorem prime_eightySixCF_12821 : Nat.Prime 12821 := by norm_num

private theorem prime_eightySixCF_12841 : Nat.Prime 12841 := by norm_num

private theorem prime_eightySixCF_13259 : Nat.Prime 13259 := by norm_num

private theorem prime_eightySixCF_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_eightySixCF_13759 : Nat.Prime 13759 := by norm_num

private theorem prime_eightySixCF_13789 : Nat.Prime 13789 := by norm_num

private theorem prime_eightySixCF_14461 : Nat.Prime 14461 := by norm_num

private theorem prime_eightySixCF_14723 : Nat.Prime 14723 := by norm_num

private theorem prime_eightySixCF_15319 : Nat.Prime 15319 := by norm_num

private theorem prime_eightySixCF_15349 : Nat.Prime 15349 := by norm_num

private theorem prime_eightySixCF_15881 : Nat.Prime 15881 := by norm_num

private theorem prime_eightySixCF_15887 : Nat.Prime 15887 := by norm_num

private theorem prime_eightySixCF_15973 : Nat.Prime 15973 := by norm_num

private theorem prime_eightySixCF_17909 : Nat.Prime 17909 := by norm_num

private theorem prime_eightySixCF_18119 : Nat.Prime 18119 := by norm_num

private theorem prime_eightySixCF_19231 : Nat.Prime 19231 := by norm_num

private theorem prime_eightySixCF_19889 : Nat.Prime 19889 := by norm_num

private theorem prime_eightySixCF_19993 : Nat.Prime 19993 := by norm_num

private theorem prime_eightySixCF_21001 : Nat.Prime 21001 := by norm_num

private theorem prime_eightySixCF_21017 : Nat.Prime 21017 := by norm_num

private theorem prime_eightySixCF_21383 : Nat.Prime 21383 := by norm_num

private theorem prime_eightySixCF_22159 : Nat.Prime 22159 := by norm_num

private theorem prime_eightySixCF_24133 : Nat.Prime 24133 := by norm_num

private theorem prime_eightySixCF_25321 : Nat.Prime 25321 := by norm_num

private theorem prime_eightySixCF_25423 : Nat.Prime 25423 := by norm_num

private theorem prime_eightySixCF_25889 : Nat.Prime 25889 := by norm_num

private theorem prime_eightySixCF_26111 : Nat.Prime 26111 := by norm_num

private theorem prime_eightySixCF_27827 : Nat.Prime 27827 := by norm_num

private theorem prime_eightySixCF_28201 : Nat.Prime 28201 := by norm_num

private theorem prime_eightySixCF_28429 : Nat.Prime 28429 := by norm_num

private theorem prime_eightySixCF_28547 : Nat.Prime 28547 := by norm_num

private theorem prime_eightySixCF_28571 : Nat.Prime 28571 := by norm_num

private theorem prime_eightySixCF_30763 : Nat.Prime 30763 := by norm_num

private theorem prime_eightySixCF_31121 : Nat.Prime 31121 := by norm_num

private theorem prime_eightySixCF_32009 : Nat.Prime 32009 := by norm_num

private theorem prime_eightySixCF_32503 : Nat.Prime 32503 := by norm_num

private theorem prime_eightySixCF_35543 : Nat.Prime 35543 := by norm_num

private theorem prime_eightySixCF_36529 : Nat.Prime 36529 := by norm_num

private theorem prime_eightySixCF_36721 : Nat.Prime 36721 := by norm_num

private theorem prime_eightySixCF_37339 : Nat.Prime 37339 := by norm_num

private theorem prime_eightySixCF_38069 : Nat.Prime 38069 := by norm_num

private theorem prime_eightySixCF_38501 : Nat.Prime 38501 := by norm_num

private theorem prime_eightySixCF_38891 : Nat.Prime 38891 := by norm_num

private theorem prime_eightySixCF_39089 : Nat.Prime 39089 := by norm_num

private theorem prime_eightySixCF_41719 : Nat.Prime 41719 := by norm_num

private theorem prime_eightySixCF_41959 : Nat.Prime 41959 := by norm_num

private theorem prime_eightySixCF_44257 : Nat.Prime 44257 := by norm_num

private theorem prime_eightySixCF_44819 : Nat.Prime 44819 := by norm_num

private theorem prime_eightySixCF_46861 : Nat.Prime 46861 := by norm_num

private theorem prime_eightySixCF_47279 : Nat.Prime 47279 := by norm_num

private theorem prime_eightySixCF_48539 : Nat.Prime 48539 := by norm_num

private theorem prime_eightySixCF_49367 : Nat.Prime 49367 := by norm_num

private theorem prime_eightySixCF_50929 : Nat.Prime 50929 := by norm_num

private theorem prime_eightySixCF_53309 : Nat.Prime 53309 := by norm_num

private theorem prime_eightySixCF_55201 : Nat.Prime 55201 := by norm_num

private theorem prime_eightySixCF_55639 : Nat.Prime 55639 := by norm_num

private theorem prime_eightySixCF_58913 : Nat.Prime 58913 := by norm_num

private theorem prime_eightySixCF_59467 : Nat.Prime 59467 := by norm_num

private theorem prime_eightySixCF_60103 : Nat.Prime 60103 := by norm_num

private theorem prime_eightySixCF_60793 : Nat.Prime 60793 := by norm_num

private theorem prime_eightySixCF_61253 : Nat.Prime 61253 := by norm_num

private theorem prime_eightySixCF_62659 : Nat.Prime 62659 := by norm_num

private theorem prime_eightySixCF_63409 : Nat.Prime 63409 := by norm_num

private theorem prime_eightySixCF_63473 : Nat.Prime 63473 := by norm_num

private theorem prime_eightySixCF_65183 : Nat.Prime 65183 := by norm_num

private theorem prime_eightySixCF_65563 : Nat.Prime 65563 := by norm_num

private theorem prime_eightySixCF_69151 : Nat.Prime 69151 := by norm_num

private theorem prime_eightySixCF_69991 : Nat.Prime 69991 := by norm_num

private theorem prime_eightySixCF_70351 : Nat.Prime 70351 := by norm_num

private theorem prime_eightySixCF_72467 : Nat.Prime 72467 := by norm_num

private theorem prime_eightySixCF_79229 : Nat.Prime 79229 := by norm_num

private theorem prime_eightySixCF_79841 : Nat.Prime 79841 := by norm_num

private theorem prime_eightySixCF_80713 : Nat.Prime 80713 := by norm_num

private theorem prime_eightySixCF_80819 : Nat.Prime 80819 := by norm_num

private theorem prime_eightySixCF_82483 : Nat.Prime 82483 := by norm_num

private theorem prime_eightySixCF_88513 : Nat.Prime 88513 := by norm_num

private theorem prime_eightySixCF_91243 : Nat.Prime 91243 := by norm_num

private theorem prime_eightySixCF_93053 : Nat.Prime 93053 := by norm_num

private theorem prime_eightySixCF_95723 : Nat.Prime 95723 := by norm_num

private theorem prime_eightySixCF_98377 : Nat.Prime 98377 := by norm_num

private theorem prime_eightySixCF_99527 : Nat.Prime 99527 := by norm_num

private theorem prime_eightySixCF_108503 : Nat.Prime 108503 := by norm_num

private theorem prime_eightySixCF_111791 : Nat.Prime 111791 := by norm_num

private theorem prime_eightySixCF_128659 : Nat.Prime 128659 := by norm_num

private theorem prime_eightySixCF_135221 : Nat.Prime 135221 := by norm_num

private theorem prime_eightySixCF_135661 : Nat.Prime 135661 := by norm_num

private theorem prime_eightySixCF_150209 : Nat.Prime 150209 := by norm_num

private theorem prime_eightySixCF_155723 : Nat.Prime 155723 := by norm_num

private theorem prime_eightySixCF_160163 : Nat.Prime 160163 := by norm_num

private theorem prime_eightySixCF_161599 : Nat.Prime 161599 := by norm_num

private theorem prime_eightySixCF_165367 : Nat.Prime 165367 := by norm_num

private theorem prime_eightySixCF_178853 : Nat.Prime 178853 := by norm_num

private theorem prime_eightySixCF_184859 : Nat.Prime 184859 := by norm_num

private theorem prime_eightySixCF_185441 : Nat.Prime 185441 := by norm_num

private theorem prime_eightySixCF_192991 : Nat.Prime 192991 := by norm_num

private theorem prime_eightySixCF_200017 : Nat.Prime 200017 := by norm_num

private theorem prime_eightySixCF_205031 : Nat.Prime 205031 := by norm_num

private theorem prime_eightySixCF_207821 : Nat.Prime 207821 := by norm_num

private theorem prime_eightySixCF_207877 : Nat.Prime 207877 := by norm_num

private theorem prime_eightySixCF_211979 : Nat.Prime 211979 := by norm_num

private theorem prime_eightySixCF_213887 : Nat.Prime 213887 := by norm_num

private theorem prime_eightySixCF_218677 : Nat.Prime 218677 := by norm_num

private theorem prime_eightySixCF_243863 : Nat.Prime 243863 := by norm_num

private theorem prime_eightySixCF_261619 : Nat.Prime 261619 := by norm_num

private theorem prime_eightySixCF_267763 : Nat.Prime 267763 := by norm_num

private theorem prime_eightySixCF_285763 : Nat.Prime 285763 := by norm_num

private theorem prime_eightySixCF_286301 : Nat.Prime 286301 := by norm_num

private theorem prime_eightySixCF_299029 : Nat.Prime 299029 := by norm_num

private theorem prime_eightySixCF_300683 : Nat.Prime 300683 := by norm_num

private theorem prime_eightySixCF_304393 : Nat.Prime 304393 := by norm_num

private theorem prime_eightySixCF_325219 : Nat.Prime 325219 := by norm_num

private theorem prime_eightySixCF_342949 : Nat.Prime 342949 := by norm_num

private theorem prime_eightySixCF_351157 : Nat.Prime 351157 := by norm_num

private theorem prime_eightySixCF_375233 : Nat.Prime 375233 := by norm_num

private theorem prime_eightySixCF_380867 : Nat.Prime 380867 := by norm_num

private theorem prime_eightySixCF_382661 : Nat.Prime 382661 := by norm_num

private theorem prime_eightySixCF_383609 : Nat.Prime 383609 := by norm_num

private theorem prime_eightySixCF_393749 : Nat.Prime 393749 := by norm_num

private theorem prime_eightySixCF_434689 : Nat.Prime 434689 := by norm_num

private theorem prime_eightySixCF_444179 : Nat.Prime 444179 := by norm_num

private theorem prime_eightySixCF_449263 : Nat.Prime 449263 := by norm_num

private theorem prime_eightySixCF_507503 : Nat.Prime 507503 := by norm_num

private theorem prime_eightySixCF_519413 : Nat.Prime 519413 := by norm_num

private theorem prime_eightySixCF_529129 : Nat.Prime 529129 := by norm_num

private theorem prime_eightySixCF_530641 : Nat.Prime 530641 := by norm_num

private theorem prime_eightySixCF_532561 : Nat.Prime 532561 := by norm_num

private theorem prime_eightySixCF_537281 : Nat.Prime 537281 := by norm_num

private theorem prime_eightySixCF_546569 : Nat.Prime 546569 := by norm_num

private theorem prime_eightySixCF_588257 : Nat.Prime 588257 := by norm_num

private theorem prime_eightySixCF_609313 : Nat.Prime 609313 := by norm_num

private theorem prime_eightySixCF_695047 : Nat.Prime 695047 := by norm_num

private theorem prime_eightySixCF_706003 : Nat.Prime 706003 := by norm_num

private theorem prime_eightySixCF_728537 : Nat.Prime 728537 := by norm_num

private theorem prime_eightySixCF_738197 : Nat.Prime 738197 := by norm_num

private theorem prime_eightySixCF_763879 : Nat.Prime 763879 := by norm_num

private theorem prime_eightySixCF_867281 : Nat.Prime 867281 := by norm_num

private theorem prime_eightySixCF_970699 : Nat.Prime 970699 := by norm_num

private theorem prime_eightySixCF_993611 : Nat.Prime 993611 := by norm_num

private theorem prime_eightySixCF_1016401 : Nat.Prime 1016401 := by norm_num

private theorem prime_eightySixCF_1074389 : Nat.Prime 1074389 := by norm_num

private theorem prime_eightySixCF_1215283 : Nat.Prime 1215283 := by norm_num

private theorem prime_eightySixCF_1237471 : Nat.Prime 1237471 := by norm_num

private theorem prime_eightySixCF_1254137 : Nat.Prime 1254137 := by norm_num

private theorem prime_eightySixCF_1279801 : Nat.Prime 1279801 := by norm_num

private theorem prime_eightySixCF_1351099 : Nat.Prime 1351099 := by norm_num

private theorem prime_eightySixCF_1369559 : Nat.Prime 1369559 := by norm_num

private theorem prime_eightySixCF_1381747 : Nat.Prime 1381747 := by norm_num

private theorem prime_eightySixCF_1512209 : Nat.Prime 1512209 := by norm_num

private theorem prime_eightySixCF_1512361 : Nat.Prime 1512361 := by norm_num

private theorem prime_eightySixCF_1528187 : Nat.Prime 1528187 := by norm_num

private theorem prime_eightySixCF_1552541 : Nat.Prime 1552541 := by norm_num

private theorem prime_eightySixCF_1680121 : Nat.Prime 1680121 := by norm_num

private theorem prime_eightySixCF_1780001 : Nat.Prime 1780001 := by norm_num

private theorem prime_eightySixCF_1866031 : Nat.Prime 1866031 := by norm_num

private theorem prime_eightySixCF_2006791 : Nat.Prime 2006791 := by norm_num

private theorem prime_eightySixCF_2009971 : Nat.Prime 2009971 := by norm_num

private theorem prime_eightySixCF_2307307 : Nat.Prime 2307307 := by norm_num

private theorem prime_eightySixCF_2321239 : Nat.Prime 2321239 := by norm_num

private theorem prime_eightySixCF_2325227 : Nat.Prime 2325227 := by norm_num

private theorem prime_eightySixCF_2463841 : Nat.Prime 2463841 := by norm_num

private theorem prime_eightySixCF_2623757 : Nat.Prime 2623757 := by norm_num

private theorem prime_eightySixCF_2652437 : Nat.Prime 2652437 := by norm_num

private theorem prime_eightySixCF_2826361 : Nat.Prime 2826361 := by norm_num

private theorem prime_eightySixCF_2922373 : Nat.Prime 2922373 := by norm_num

private theorem prime_eightySixCF_2996393 : Nat.Prime 2996393 := by norm_num

private theorem prime_eightySixCF_3012871 : Nat.Prime 3012871 := by norm_num

private theorem prime_eightySixCF_3064561 : Nat.Prime 3064561 := by norm_num

private theorem prime_eightySixCF_3166183 : Nat.Prime 3166183 := by norm_num

private theorem prime_eightySixCF_3329761 : Nat.Prime 3329761 := by norm_num

private theorem prime_eightySixCF_3410369 : Nat.Prime 3410369 := by norm_num

private theorem prime_eightySixCF_3508529 : Nat.Prime 3508529 := by norm_num

private theorem prime_eightySixCF_3599207 : Nat.Prime 3599207 := by norm_num

private theorem prime_eightySixCF_3783119 : Nat.Prime 3783119 := by norm_num

private theorem prime_eightySixCF_3896491 : Nat.Prime 3896491 := by norm_num

private theorem prime_eightySixCF_4296829 : Nat.Prime 4296829 := by norm_num

private theorem prime_eightySixCF_4336777 : Nat.Prime 4336777 := by norm_num

private theorem prime_eightySixCF_4518499 : Nat.Prime 4518499 := by norm_num

private theorem prime_eightySixCF_4578467 : Nat.Prime 4578467 := by norm_num

private theorem prime_eightySixCF_4675103 : Nat.Prime 4675103 := by norm_num

private theorem prime_eightySixCF_4684213 : Nat.Prime 4684213 := by norm_num

private theorem prime_eightySixCF_5086793 : Nat.Prime 5086793 := by norm_num

private theorem prime_eightySixCF_5359537 : Nat.Prime 5359537 := by norm_num

private theorem prime_eightySixCF_6099983 : Nat.Prime 6099983 := by norm_num

private theorem prime_eightySixCF_6196019 : Nat.Prime 6196019 := by norm_num

private theorem prime_eightySixCF_6401387 : Nat.Prime 6401387 := by norm_num

private theorem prime_eightySixCF_6565463 : Nat.Prime 6565463 := by norm_num

private theorem prime_eightySixCF_6737803 : Nat.Prime 6737803 := by norm_num

private theorem prime_eightySixCF_6899863 : Nat.Prime 6899863 := by norm_num

private theorem prime_eightySixCF_7374883 : Nat.Prime 7374883 := by norm_num

private theorem prime_eightySixCF_7986047 : Nat.Prime 7986047 := by norm_num

private theorem prime_eightySixCF_8077661 : Nat.Prime 8077661 := by norm_num

private theorem prime_eightySixCF_8206927 : Nat.Prime 8206927 := by norm_num

private theorem prime_eightySixCF_8954713 : Nat.Prime 8954713 := by norm_num

private theorem prime_eightySixCF_9178987 : Nat.Prime 9178987 := by norm_num

private theorem prime_eightySixCF_9498301 : Nat.Prime 9498301 := by norm_num

private theorem prime_eightySixCF_9510167 : Nat.Prime 9510167 := by norm_num

private theorem prime_eightySixCF_9910123 : Nat.Prime 9910123 := by norm_num

private theorem prime_eightySixCF_10519153 : Nat.Prime 10519153 := by norm_num

private theorem prime_eightySixCF_11486989 : Nat.Prime 11486989 := by norm_num

private theorem prime_eightySixCF_11712763 : Nat.Prime 11712763 := by norm_num

private theorem prime_eightySixCF_12452749 : Nat.Prime 12452749 := by norm_num

private theorem prime_eightySixCF_12742321 : Nat.Prime 12742321 := by norm_num

private theorem prime_eightySixCF_13133279 : Nat.Prime 13133279 := by norm_num

private theorem prime_eightySixCF_13866877 : Nat.Prime 13866877 := by norm_num

private theorem prime_eightySixCF_14050457 : Nat.Prime 14050457 := by norm_num

private theorem prime_eightySixCF_15164179 : Nat.Prime 15164179 := by norm_num

private theorem prime_eightySixCF_16269601 : Nat.Prime 16269601 := by norm_num

private theorem prime_eightySixCF_17012323 : Nat.Prime 17012323 := by norm_num

private theorem prime_eightySixCF_17384359 : Nat.Prime 17384359 := by norm_num

private theorem prime_eightySixCF_17553637 : Nat.Prime 17553637 := by norm_num

private theorem prime_eightySixCF_21583087 : Nat.Prime 21583087 := by norm_num

private theorem prime_eightySixCF_22757179 : Nat.Prime 22757179 := by norm_num

private theorem prime_eightySixCF_23439739 : Nat.Prime 23439739 := by norm_num

private theorem prime_eightySixCF_24207923 : Nat.Prime 24207923 := by norm_num

private theorem prime_eightySixCF_24776239 : Nat.Prime 24776239 := by norm_num

private theorem prime_eightySixCF_24999179 : Nat.Prime 24999179 := by norm_num

private theorem prime_eightySixCF_25728553 : Nat.Prime 25728553 := by norm_num

private theorem prime_eightySixCF_27269527 : Nat.Prime 27269527 := by norm_num

private theorem prime_eightySixCF_28896919 : Nat.Prime 28896919 := by norm_num

private theorem prime_eightySixCF_31706881 : Nat.Prime 31706881 := by
  apply lucas_primality 31706881 (14 : ZMod 31706881)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (23, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (23, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 31706881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 31706881) ^ 15853440 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (14 : ZMod 31706881) ^ 10568960 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (14 : ZMod 31706881) ^ 6341376 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (14 : ZMod 31706881) ^ 1378560 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (14 : ZMod 31706881) ^ 88320 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_32055851 : Nat.Prime 32055851 := by
  apply lucas_primality 32055851 (2 : ZMod 32055851)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (41, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (41, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 32055851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32055851) ^ 16027925 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32055851) ^ 6411170 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32055851) ^ 1687150 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32055851) ^ 781850 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32055851) ^ 38950 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_32607563 : Nat.Prime 32607563 := by
  apply lucas_primality 32607563 (2 : ZMod 32607563)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1254137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1254137, 1)] : List FactorBlock).map factorBlockValue).prod) = 32607563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_1254137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32607563) ^ 16303781 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32607563) ^ 2508274 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32607563) ^ 26 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_32827709 : Nat.Prime 32827709 := by
  apply lucas_primality 32827709 (2 : ZMod 32827709)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8206927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8206927, 1)] : List FactorBlock).map factorBlockValue).prod) = 32827709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_8206927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 32827709) ^ 16413854 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32827709) ^ 4 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_34239437 : Nat.Prime 34239437 := by
  apply lucas_primality 34239437 (3 : ZMod 34239437)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (15881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (15881, 1)] : List FactorBlock).map factorBlockValue).prod) = 34239437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_15881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34239437) ^ 17119718 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 34239437) ^ 4891348 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 34239437) ^ 3112676 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 34239437) ^ 2156 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_34554089 : Nat.Prime 34554089 := by
  apply lucas_primality 34554089 (3 : ZMod 34554089)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (277, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (277, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 34554089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_277
      · exact prime_eightySixCF_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34554089) ^ 17277044 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 34554089) ^ 1114648 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 34554089) ^ 124744 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 34554089) ^ 68696 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_36081961 : Nat.Prime 36081961 := by
  apply lucas_primality 36081961 (7 : ZMod 36081961)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (300683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (300683, 1)] : List FactorBlock).map factorBlockValue).prod) = 36081961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_300683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36081961) ^ 18040980 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 36081961) ^ 12027320 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 36081961) ^ 7216392 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 36081961) ^ 120 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_40587413 : Nat.Prime 40587413 := by
  apply lucas_primality 40587413 (2 : ZMod 40587413)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (317, 1), (32009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (317, 1), (32009, 1)] : List FactorBlock).map factorBlockValue).prod) = 40587413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_317
      · exact prime_eightySixCF_32009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40587413) ^ 20293706 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 40587413) ^ 128036 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 40587413) ^ 1268 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_45545387 : Nat.Prime 45545387 := by
  apply lucas_primality 45545387 (2 : ZMod 45545387)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (157, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (157, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) = 45545387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_157
      · exact prime_eightySixCF_4679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45545387) ^ 22772693 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45545387) ^ 1469206 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45545387) ^ 290098 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45545387) ^ 9734 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_47350271 : Nat.Prime 47350271 := by
  apply lucas_primality 47350271 (11 : ZMod 47350271)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17, 1), (25321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17, 1), (25321, 1)] : List FactorBlock).map factorBlockValue).prod) = 47350271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_25321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 47350271) ^ 23675135 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 47350271) ^ 9470054 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 47350271) ^ 4304570 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 47350271) ^ 2785310 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 47350271) ^ 1870 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_52309393 : Nat.Prime 52309393 := by
  apply lucas_primality 52309393 (5 : ZMod 52309393)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (71, 1), (15349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (71, 1), (15349, 1)] : List FactorBlock).map factorBlockValue).prod) = 52309393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_71
      · exact prime_eightySixCF_15349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52309393) ^ 26154696 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52309393) ^ 17436464 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52309393) ^ 736752 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52309393) ^ 3408 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_56261077 : Nat.Prime 56261077 := by
  apply lucas_primality 56261077 (6 : ZMod 56261077)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (727, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (727, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) = 56261077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_727
      · exact prime_eightySixCF_6449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 56261077) ^ 28130538 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 56261077) ^ 18753692 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 56261077) ^ 77388 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 56261077) ^ 8724 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_57061003 : Nat.Prime 57061003 := by
  apply lucas_primality 57061003 (3 : ZMod 57061003)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9510167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9510167, 1)] : List FactorBlock).map factorBlockValue).prod) = 57061003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_9510167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 57061003) ^ 28530501 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 57061003) ^ 19020334 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 57061003) ^ 6 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_59657597 : Nat.Prime 59657597 := by
  apply lucas_primality 59657597 (2 : ZMod 59657597)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1013, 1), (14723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1013, 1), (14723, 1)] : List FactorBlock).map factorBlockValue).prod) = 59657597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_1013
      · exact prime_eightySixCF_14723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59657597) ^ 29828798 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59657597) ^ 58892 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59657597) ^ 4052 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_59935699 : Nat.Prime 59935699 := by
  apply lucas_primality 59935699 (14 : ZMod 59935699)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3329761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3329761, 1)] : List FactorBlock).map factorBlockValue).prod) = 59935699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_3329761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 59935699) ^ 29967849 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (14 : ZMod 59935699) ^ 19978566 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (14 : ZMod 59935699) ^ 18 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_60865621 : Nat.Prime 60865621 := by
  apply lucas_primality 60865621 (2 : ZMod 60865621)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (223, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (223, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod) = 60865621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_223
      · exact prime_eightySixCF_4549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60865621) ^ 30432810 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60865621) ^ 20288540 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60865621) ^ 12173124 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60865621) ^ 272940 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60865621) ^ 13380 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_64111703 : Nat.Prime 64111703 := by
  apply lucas_primality 64111703 (5 : ZMod 64111703)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32055851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32055851, 1)] : List FactorBlock).map factorBlockValue).prod) = 64111703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_32055851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64111703) ^ 32055851 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 64111703) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_78061987 : Nat.Prime 78061987 := by
  apply lucas_primality 78061987 (2 : ZMod 78061987)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4336777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4336777, 1)] : List FactorBlock).map factorBlockValue).prod) = 78061987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_4336777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78061987) ^ 39030993 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78061987) ^ 26020662 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78061987) ^ 18 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_81337001 : Nat.Prime 81337001 := by
  apply lucas_primality 81337001 (3 : ZMod 81337001)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (163, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (163, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 81337001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_163
      · exact prime_eightySixCF_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 81337001) ^ 40668500 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 81337001) ^ 16267400 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 81337001) ^ 499000 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 81337001) ^ 163000 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_90933649 : Nat.Prime 90933649 := by
  apply lucas_primality 90933649 (17 : ZMod 90933649)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (43, 1), (3389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (43, 1), (3389, 1)] : List FactorBlock).map factorBlockValue).prod) = 90933649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_3389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 90933649) ^ 45466824 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 90933649) ^ 30311216 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 90933649) ^ 6994896 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 90933649) ^ 2114736 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 90933649) ^ 26832 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_102632531 : Nat.Prime 102632531 := by
  apply lucas_primality 102632531 (2 : ZMod 102632531)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (13, 1), (10253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (13, 1), (10253, 1)] : List FactorBlock).map factorBlockValue).prod) = 102632531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_10253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102632531) ^ 51316265 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102632531) ^ 20526506 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102632531) ^ 14661790 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102632531) ^ 9330230 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102632531) ^ 7894810 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 102632531) ^ 10010 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_105066233 : Nat.Prime 105066233 := by
  apply lucas_primality 105066233 (3 : ZMod 105066233)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13133279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13133279, 1)] : List FactorBlock).map factorBlockValue).prod) = 105066233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13133279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 105066233) ^ 52533116 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 105066233) ^ 8 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_110136469 : Nat.Prime 110136469 := by
  apply lucas_primality 110136469 (2 : ZMod 110136469)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (706003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (706003, 1)] : List FactorBlock).map factorBlockValue).prod) = 110136469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_706003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110136469) ^ 55068234 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 110136469) ^ 36712156 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 110136469) ^ 8472036 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 110136469) ^ 156 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_111804659 : Nat.Prime 111804659 := by
  apply lucas_primality 111804659 (2 : ZMod 111804659)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7986047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7986047, 1)] : List FactorBlock).map factorBlockValue).prod) = 111804659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_7986047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111804659) ^ 55902329 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111804659) ^ 15972094 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 111804659) ^ 14 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_115587677 : Nat.Prime 115587677 := by
  apply lucas_primality 115587677 (2 : ZMod 115587677)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (28896919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (28896919, 1)] : List FactorBlock).map factorBlockValue).prod) = 115587677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_28896919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 115587677) ^ 57793838 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 115587677) ^ 4 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_119991719 : Nat.Prime 119991719 := by
  apply lucas_primality 119991719 (7 : ZMod 119991719)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (389, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (389, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) = 119991719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_389
      · exact prime_eightySixCF_2003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 119991719) ^ 59995859 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 119991719) ^ 17141674 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 119991719) ^ 10908338 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 119991719) ^ 308462 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 119991719) ^ 59906 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_131653631 : Nat.Prime 131653631 := by
  apply lucas_primality 131653631 (7 : ZMod 131653631)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1259, 1), (10457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1259, 1), (10457, 1)] : List FactorBlock).map factorBlockValue).prod) = 131653631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_1259
      · exact prime_eightySixCF_10457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 131653631) ^ 65826815 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 131653631) ^ 26330726 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 131653631) ^ 104570 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 131653631) ^ 12590 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_139387147 : Nat.Prime 139387147 := by
  apply lucas_primality 139387147 (3 : ZMod 139387147)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (393749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (393749, 1)] : List FactorBlock).map factorBlockValue).prod) = 139387147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_59
      · exact prime_eightySixCF_393749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 139387147) ^ 69693573 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 139387147) ^ 46462382 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 139387147) ^ 2362494 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 139387147) ^ 354 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_145619321 : Nat.Prime 145619321 := by
  apply lucas_primality 145619321 (3 : ZMod 145619321)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (47279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (47279, 1)] : List FactorBlock).map factorBlockValue).prod) = 145619321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_47279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 145619321) ^ 72809660 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 145619321) ^ 29123864 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 145619321) ^ 20802760 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 145619321) ^ 13238120 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 145619321) ^ 3080 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_149603297 : Nat.Prime 149603297 := by
  apply lucas_primality 149603297 (3 : ZMod 149603297)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (4675103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (4675103, 1)] : List FactorBlock).map factorBlockValue).prod) = 149603297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_4675103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 149603297) ^ 74801648 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 149603297) ^ 32 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_150598681 : Nat.Prime 150598681 := by
  apply lucas_primality 150598681 (22 : ZMod 150598681)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (59, 1), (89, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (59, 1), (89, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 150598681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_59
      · exact prime_eightySixCF_89
      · exact prime_eightySixCF_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 150598681) ^ 75299340 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (22 : ZMod 150598681) ^ 50199560 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (22 : ZMod 150598681) ^ 30119736 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (22 : ZMod 150598681) ^ 2552520 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (22 : ZMod 150598681) ^ 1692120 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (22 : ZMod 150598681) ^ 630120 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_154523153 : Nat.Prime 154523153 := by
  apply lucas_primality 154523153 (3 : ZMod 154523153)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (487, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (487, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) = 154523153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_487
      · exact prime_eightySixCF_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 154523153) ^ 77261576 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 154523153) ^ 22074736 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 154523153) ^ 317296 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 154523153) ^ 54544 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_188538209 : Nat.Prime 188538209 := by
  apply lucas_primality 188538209 (3 : ZMod 188538209)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (439, 1), (13421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (439, 1), (13421, 1)] : List FactorBlock).map factorBlockValue).prod) = 188538209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_439
      · exact prime_eightySixCF_13421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 188538209) ^ 94269104 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 188538209) ^ 429472 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 188538209) ^ 14048 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_190730851 : Nat.Prime 190730851 := by
  apply lucas_primality 190730851 (2 : ZMod 190730851)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (71, 1), (17909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (71, 1), (17909, 1)] : List FactorBlock).map factorBlockValue).prod) = 190730851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_71
      · exact prime_eightySixCF_17909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 190730851) ^ 95365425 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 190730851) ^ 63576950 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 190730851) ^ 38146170 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 190730851) ^ 2686350 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 190730851) ^ 10650 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_198272609 : Nat.Prime 198272609 := by
  apply lucas_primality 198272609 (3 : ZMod 198272609)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (6196019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (6196019, 1)] : List FactorBlock).map factorBlockValue).prod) = 198272609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_6196019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 198272609) ^ 99136304 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 198272609) ^ 32 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_208234667 : Nat.Prime 208234667 := by
  apply lucas_primality 208234667 (2 : ZMod 208234667)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (743, 1), (8243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (743, 1), (8243, 1)] : List FactorBlock).map factorBlockValue).prod) = 208234667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_743
      · exact prime_eightySixCF_8243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 208234667) ^ 104117333 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 208234667) ^ 12249098 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 208234667) ^ 280262 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 208234667) ^ 25262 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_222832639 : Nat.Prime 222832639 := by
  apply lucas_primality 222832639 (7 : ZMod 222832639)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (199, 1), (8887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (199, 1), (8887, 1)] : List FactorBlock).map factorBlockValue).prod) = 222832639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_199
      · exact prime_eightySixCF_8887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 222832639) ^ 111416319 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 222832639) ^ 74277546 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 222832639) ^ 31833234 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 222832639) ^ 1119762 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 222832639) ^ 25074 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_223609319 : Nat.Prime 223609319 := by
  apply lucas_primality 223609319 (13 : ZMod 223609319)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (111804659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (111804659, 1)] : List FactorBlock).map factorBlockValue).prod) = 223609319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_111804659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 223609319) ^ 111804659 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 223609319) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_224769277 : Nat.Prime 224769277 := by
  apply lucas_primality 224769277 (2 : ZMod 224769277)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (131, 1), (15887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (131, 1), (15887, 1)] : List FactorBlock).map factorBlockValue).prod) = 224769277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_131
      · exact prime_eightySixCF_15887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224769277) ^ 112384638 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 224769277) ^ 74923092 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 224769277) ^ 1715796 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 224769277) ^ 14148 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_247049189 : Nat.Prime 247049189 := by
  apply lucas_primality 247049189 (2 : ZMod 247049189)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (546569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (546569, 1)] : List FactorBlock).map factorBlockValue).prod) = 247049189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_113
      · exact prime_eightySixCF_546569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 247049189) ^ 123524594 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 247049189) ^ 2186276 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 247049189) ^ 452 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_247822231 : Nat.Prime 247822231 := by
  apply lucas_primality 247822231 (3 : ZMod 247822231)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (99527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (99527, 1)] : List FactorBlock).map factorBlockValue).prod) = 247822231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_83
      · exact prime_eightySixCF_99527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 247822231) ^ 123911115 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 247822231) ^ 82607410 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 247822231) ^ 49564446 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 247822231) ^ 2985810 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 247822231) ^ 2490 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_272140931 : Nat.Prime 272140931 := by
  apply lucas_primality 272140931 (2 : ZMod 272140931)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29, 1), (55201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29, 1), (55201, 1)] : List FactorBlock).map factorBlockValue).prod) = 272140931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_29
      · exact prime_eightySixCF_55201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 272140931) ^ 136070465 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 272140931) ^ 54428186 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 272140931) ^ 16008290 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 272140931) ^ 9384170 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 272140931) ^ 4930 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_275749447 : Nat.Prime 275749447 := by
  apply lucas_primality 275749447 (3 : ZMod 275749447)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (6565463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (6565463, 1)] : List FactorBlock).map factorBlockValue).prod) = 275749447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_6565463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 275749447) ^ 137874723 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 275749447) ^ 91916482 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 275749447) ^ 39392778 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 275749447) ^ 42 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_283856533 : Nat.Prime 283856533 := by
  apply lucas_primality 283856533 (2 : ZMod 283856533)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (243863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (243863, 1)] : List FactorBlock).map factorBlockValue).prod) = 283856533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_97
      · exact prime_eightySixCF_243863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 283856533) ^ 141928266 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 283856533) ^ 94618844 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 283856533) ^ 2926356 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 283856533) ^ 1164 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_287280313 : Nat.Prime 287280313 := by
  apply lucas_primality 287280313 (7 : ZMod 287280313)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (839, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (839, 1), (1297, 1)] : List FactorBlock).map factorBlockValue).prod) = 287280313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_839
      · exact prime_eightySixCF_1297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 287280313) ^ 143640156 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 287280313) ^ 95760104 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 287280313) ^ 26116392 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 287280313) ^ 342408 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 287280313) ^ 221496 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_292324507 : Nat.Prime 292324507 := by
  apply lucas_primality 292324507 (3 : ZMod 292324507)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (83, 1), (103, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (83, 1), (103, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 292324507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_83
      · exact prime_eightySixCF_103
      · exact prime_eightySixCF_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 292324507) ^ 146162253 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 292324507) ^ 97441502 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 292324507) ^ 7129866 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 292324507) ^ 3521982 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 292324507) ^ 2838102 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 292324507) ^ 2103054 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_310443967 : Nat.Prime 310443967 := by
  apply lucas_primality 310443967 (5 : ZMod 310443967)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2463841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2463841, 1)] : List FactorBlock).map factorBlockValue).prod) = 310443967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_2463841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 310443967) ^ 155221983 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 310443967) ^ 103481322 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 310443967) ^ 44349138 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 310443967) ^ 126 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_348455281 : Nat.Prime 348455281 := by
  apply lucas_primality 348455281 (7 : ZMod 348455281)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (73, 1), (19889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (73, 1), (19889, 1)] : List FactorBlock).map factorBlockValue).prod) = 348455281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_73
      · exact prime_eightySixCF_19889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 348455281) ^ 174227640 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 348455281) ^ 116151760 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 348455281) ^ 69691056 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 348455281) ^ 4773360 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 348455281) ^ 17520 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_358477673 : Nat.Prime 358477673 := by
  apply lucas_primality 358477673 (3 : ZMod 358477673)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (6401387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (6401387, 1)] : List FactorBlock).map factorBlockValue).prod) = 358477673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_6401387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 358477673) ^ 179238836 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 358477673) ^ 51211096 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 358477673) ^ 56 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_366911537 : Nat.Prime 366911537 := by
  apply lucas_primality 366911537 (3 : ZMod 366911537)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (37, 1), (19993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (37, 1), (19993, 1)] : List FactorBlock).map factorBlockValue).prod) = 366911537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_19993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 366911537) ^ 183455768 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 366911537) ^ 11835856 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 366911537) ^ 9916528 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 366911537) ^ 18352 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_436312433 : Nat.Prime 436312433 := by
  apply lucas_primality 436312433 (3 : ZMod 436312433)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27269527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27269527, 1)] : List FactorBlock).map factorBlockValue).prod) = 436312433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_27269527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 436312433) ^ 218156216 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436312433) ^ 16 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_455548829 : Nat.Prime 455548829 := by
  apply lucas_primality 455548829 (2 : ZMod 455548829)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (16269601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (16269601, 1)] : List FactorBlock).map factorBlockValue).prod) = 455548829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_16269601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 455548829) ^ 227774414 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 455548829) ^ 65078404 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 455548829) ^ 28 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_477663757 : Nat.Prime 477663757 := by
  apply lucas_primality 477663757 (2 : ZMod 477663757)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (29, 1), (263, 1), (307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (29, 1), (263, 1), (307, 1)] : List FactorBlock).map factorBlockValue).prod) = 477663757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_29
      · exact prime_eightySixCF_263
      · exact prime_eightySixCF_307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 477663757) ^ 238831878 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 477663757) ^ 159221252 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 477663757) ^ 28097868 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 477663757) ^ 16471164 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 477663757) ^ 1816212 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 477663757) ^ 1555908 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_494098379 : Nat.Prime 494098379 := by
  apply lucas_primality 494098379 (2 : ZMod 494098379)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (247049189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (247049189, 1)] : List FactorBlock).map factorBlockValue).prod) = 494098379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_247049189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 494098379) ^ 247049189 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 494098379) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_504962831 : Nat.Prime 504962831 := by
  apply lucas_primality 504962831 (7 : ZMod 504962831)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (1074389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (1074389, 1)] : List FactorBlock).map factorBlockValue).prod) = 504962831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_47
      · exact prime_eightySixCF_1074389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 504962831) ^ 252481415 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 504962831) ^ 100992566 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 504962831) ^ 10743890 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 504962831) ^ 470 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_507605291 : Nat.Prime 507605291 := by
  apply lucas_primality 507605291 (2 : ZMod 507605291)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4241, 1), (11969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4241, 1), (11969, 1)] : List FactorBlock).map factorBlockValue).prod) = 507605291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_4241
      · exact prime_eightySixCF_11969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 507605291) ^ 253802645 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 507605291) ^ 101521058 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 507605291) ^ 119690 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 507605291) ^ 42410 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_535177483 : Nat.Prime 535177483 := by
  apply lucas_primality 535177483 (2 : ZMod 535177483)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12742321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12742321, 1)] : List FactorBlock).map factorBlockValue).prod) = 535177483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_12742321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 535177483) ^ 267588741 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 535177483) ^ 178392494 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 535177483) ^ 76453926 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 535177483) ^ 42 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_591387427 : Nat.Prime 591387427 := by
  apply lucas_primality 591387427 (2 : ZMod 591387427)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (19, 1), (67, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (19, 1), (67, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 591387427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_67
      · exact prime_eightySixCF_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 591387427) ^ 295693713 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591387427) ^ 197129142 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591387427) ^ 84483918 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591387427) ^ 31125654 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591387427) ^ 8826678 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591387427) ^ 481194 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_726011249 : Nat.Prime 726011249 := by
  apply lucas_primality 726011249 (3 : ZMod 726011249)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (127, 1), (21017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (127, 1), (21017, 1)] : List FactorBlock).map factorBlockValue).prod) = 726011249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_127
      · exact prime_eightySixCF_21017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 726011249) ^ 363005624 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 726011249) ^ 42706544 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 726011249) ^ 5716624 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 726011249) ^ 34544 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_751656937 : Nat.Prime 751656937 := by
  apply lucas_primality 751656937 (5 : ZMod 751656937)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (763879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (763879, 1)] : List FactorBlock).map factorBlockValue).prod) = 751656937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_763879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 751656937) ^ 375828468 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 751656937) ^ 250552312 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 751656937) ^ 18333096 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 751656937) ^ 984 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_797296343 : Nat.Prime 797296343 := by
  apply lucas_primality 797296343 (5 : ZMod 797296343)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1823, 1), (218677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1823, 1), (218677, 1)] : List FactorBlock).map factorBlockValue).prod) = 797296343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_1823
      · exact prime_eightySixCF_218677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 797296343) ^ 398648171 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 797296343) ^ 437354 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 797296343) ^ 3646 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_911097659 : Nat.Prime 911097659 := by
  apply lucas_primality 911097659 (2 : ZMod 911097659)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (455548829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (455548829, 1)] : List FactorBlock).map factorBlockValue).prod) = 911097659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_455548829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 911097659) ^ 455548829 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 911097659) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_936380891 : Nat.Prime 936380891 := by
  apply lucas_primality 936380891 (2 : ZMod 936380891)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (863, 1), (108503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (863, 1), (108503, 1)] : List FactorBlock).map factorBlockValue).prod) = 936380891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_863
      · exact prime_eightySixCF_108503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 936380891) ^ 468190445 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 936380891) ^ 187276178 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 936380891) ^ 1085030 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 936380891) ^ 8630 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1000235399 : Nat.Prime 1000235399 := by
  apply lucas_primality 1000235399 (7 : ZMod 1000235399)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (53, 1), (304393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (53, 1), (304393, 1)] : List FactorBlock).map factorBlockValue).prod) = 1000235399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_53
      · exact prime_eightySixCF_304393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1000235399) ^ 500117699 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1000235399) ^ 32265658 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1000235399) ^ 18872366 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1000235399) ^ 3286 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1015210583 : Nat.Prime 1015210583 := by
  apply lucas_primality 1015210583 (5 : ZMod 1015210583)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (507605291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (507605291, 1)] : List FactorBlock).map factorBlockValue).prod) = 1015210583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_507605291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1015210583) ^ 507605291 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1015210583) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1033184701 : Nat.Prime 1033184701 := by
  apply lucas_primality 1033184701 (2 : ZMod 1033184701)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (382661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (382661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1033184701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_382661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1033184701) ^ 516592350 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033184701) ^ 344394900 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033184701) ^ 206636940 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033184701) ^ 2700 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1045021633 : Nat.Prime 1045021633 := by
  apply lucas_primality 1045021633 (7 : ZMod 1045021633)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (149, 1), (36529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (149, 1), (36529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1045021633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_149
      · exact prime_eightySixCF_36529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1045021633) ^ 522510816 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1045021633) ^ 348340544 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1045021633) ^ 7013568 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1045021633) ^ 28608 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1184803733 : Nat.Prime 1184803733 := by
  apply lucas_primality 1184803733 (2 : ZMod 1184803733)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (41, 1), (61, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (41, 1), (61, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1184803733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_61
      · exact prime_eightySixCF_2417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1184803733) ^ 592401866 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1184803733) ^ 169257676 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1184803733) ^ 28897652 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1184803733) ^ 19423012 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1184803733) ^ 490196 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1430693507 : Nat.Prime 1430693507 := by
  apply lucas_primality 1430693507 (2 : ZMod 1430693507)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (1512361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (1512361, 1)] : List FactorBlock).map factorBlockValue).prod) = 1430693507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_1512361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1430693507) ^ 715346753 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1430693507) ^ 130063046 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1430693507) ^ 33271942 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1430693507) ^ 946 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1697366299 : Nat.Prime 1697366299 := by
  apply lucas_primality 1697366299 (10 : ZMod 1697366299)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (6899863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (6899863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1697366299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_6899863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1697366299) ^ 848683149 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1697366299) ^ 565788766 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1697366299) ^ 41399178 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1697366299) ^ 246 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1718779177 : Nat.Prime 1718779177 := by
  apply lucas_primality 1718779177 (7 : ZMod 1718779177)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (2652437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (2652437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1718779177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_2652437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1718779177) ^ 859389588 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1718779177) ^ 572926392 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1718779177) ^ 648 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1753947043 : Nat.Prime 1753947043 := by
  apply lucas_primality 1753947043 (3 : ZMod 1753947043)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (292324507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (292324507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1753947043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_292324507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1753947043) ^ 876973521 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1753947043) ^ 584649014 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1753947043) ^ 6 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1765793479 : Nat.Prime 1765793479 := by
  apply lucas_primality 1765793479 (3 : ZMod 1765793479)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (103, 1), (60793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (103, 1), (60793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1765793479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_47
      · exact prime_eightySixCF_103
      · exact prime_eightySixCF_60793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1765793479) ^ 882896739 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1765793479) ^ 588597826 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1765793479) ^ 37570074 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1765793479) ^ 17143626 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1765793479) ^ 29046 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1955370029 : Nat.Prime 1955370029 := by
  apply lucas_primality 1955370029 (2 : ZMod 1955370029)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (25728553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (25728553, 1)] : List FactorBlock).map factorBlockValue).prod) = 1955370029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_25728553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1955370029) ^ 977685014 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955370029) ^ 102914212 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955370029) ^ 76 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1979261701 : Nat.Prime 1979261701 := by
  apply lucas_primality 1979261701 (6 : ZMod 1979261701)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (507503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (507503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1979261701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_507503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1979261701) ^ 989630850 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1979261701) ^ 659753900 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1979261701) ^ 395852340 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1979261701) ^ 152250900 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1979261701) ^ 3900 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2083387781 : Nat.Prime 2083387781 := by
  apply lucas_primality 2083387781 (2 : ZMod 2083387781)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (67, 1), (113, 1), (13759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (67, 1), (113, 1), (13759, 1)] : List FactorBlock).map factorBlockValue).prod) = 2083387781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_67
      · exact prime_eightySixCF_113
      · exact prime_eightySixCF_13759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2083387781) ^ 1041693890 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2083387781) ^ 416677556 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2083387781) ^ 31095340 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2083387781) ^ 18437060 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2083387781) ^ 151420 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2089626221 : Nat.Prime 2089626221 := by
  apply lucas_primality 2089626221 (2 : ZMod 2089626221)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (9498301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (9498301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2089626221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_9498301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2089626221) ^ 1044813110 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2089626221) ^ 417925244 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2089626221) ^ 189966020 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2089626221) ^ 220 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2251554997 : Nat.Prime 2251554997 := by
  apply lucas_primality 2251554997 (2 : ZMod 2251554997)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (137, 1), (1369559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (137, 1), (1369559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2251554997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_137
      · exact prime_eightySixCF_1369559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2251554997) ^ 1125777498 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2251554997) ^ 750518332 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2251554997) ^ 16434708 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2251554997) ^ 1644 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2451028841 : Nat.Prime 2451028841 := by
  apply lucas_primality 2451028841 (3 : ZMod 2451028841)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (67, 1), (70351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (67, 1), (70351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2451028841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_67
      · exact prime_eightySixCF_70351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2451028841) ^ 1225514420 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451028841) ^ 490205768 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451028841) ^ 188540680 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451028841) ^ 36582520 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2451028841) ^ 34840 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2717832443 : Nat.Prime 2717832443 := by
  apply lucas_primality 2717832443 (5 : ZMod 2717832443)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (271, 1), (499, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (271, 1), (499, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 2717832443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_271
      · exact prime_eightySixCF_499
      · exact prime_eightySixCF_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2717832443) ^ 1358916221 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2717832443) ^ 209064034 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2717832443) ^ 10028902 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2717832443) ^ 5446558 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2717832443) ^ 3515954 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_3300316727 : Nat.Prime 3300316727 := by
  apply lucas_primality 3300316727 (5 : ZMod 3300316727)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (13866877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (13866877, 1)] : List FactorBlock).map factorBlockValue).prod) = 3300316727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_13866877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3300316727) ^ 1650158363 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3300316727) ^ 471473818 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3300316727) ^ 194136278 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3300316727) ^ 238 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_3720465179 : Nat.Prime 3720465179 := by
  apply lucas_primality 3720465179 (2 : ZMod 3720465179)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (71, 1), (609313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (71, 1), (609313, 1)] : List FactorBlock).map factorBlockValue).prod) = 3720465179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_71
      · exact prime_eightySixCF_609313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3720465179) ^ 1860232589 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3720465179) ^ 86522446 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3720465179) ^ 52400918 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3720465179) ^ 6106 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_3916638493 : Nat.Prime 3916638493 := by
  apply lucas_primality 3916638493 (2 : ZMod 3916638493)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (241, 1), (5483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (241, 1), (5483, 1)] : List FactorBlock).map factorBlockValue).prod) = 3916638493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_241
      · exact prime_eightySixCF_5483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3916638493) ^ 1958319246 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3916638493) ^ 1305546164 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3916638493) ^ 301279884 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3916638493) ^ 206138868 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3916638493) ^ 16251612 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3916638493) ^ 714324 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_3974925587 : Nat.Prime 3974925587 := by
  apply lucas_primality 3974925587 (2 : ZMod 3974925587)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (64111703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (64111703, 1)] : List FactorBlock).map factorBlockValue).prod) = 3974925587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_64111703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3974925587) ^ 1987462793 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3974925587) ^ 128223406 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3974925587) ^ 62 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_4245588169 : Nat.Prime 4245588169 := by
  apply lucas_primality 4245588169 (23 : ZMod 4245588169)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (6099983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (6099983, 1)] : List FactorBlock).map factorBlockValue).prod) = 4245588169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_29
      · exact prime_eightySixCF_6099983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 4245588169) ^ 2122794084 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (23 : ZMod 4245588169) ^ 1415196056 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (23 : ZMod 4245588169) ^ 146399592 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (23 : ZMod 4245588169) ^ 696 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_4632373687 : Nat.Prime 4632373687 := by
  apply lucas_primality 4632373687 (3 : ZMod 4632373687)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (499, 1), (15319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (499, 1), (15319, 1)] : List FactorBlock).map factorBlockValue).prod) = 4632373687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_101
      · exact prime_eightySixCF_499
      · exact prime_eightySixCF_15319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4632373687) ^ 2316186843 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4632373687) ^ 1544124562 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4632373687) ^ 45865086 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4632373687) ^ 9283314 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4632373687) ^ 302394 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_4667376139 : Nat.Prime 4667376139 := by
  apply lucas_primality 4667376139 (10 : ZMod 4667376139)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (463, 1), (1680121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (463, 1), (1680121, 1)] : List FactorBlock).map factorBlockValue).prod) = 4667376139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_463
      · exact prime_eightySixCF_1680121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 4667376139) ^ 2333688069 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 4667376139) ^ 1555792046 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 4667376139) ^ 10080726 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 4667376139) ^ 2778 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5435664887 : Nat.Prime 5435664887 := by
  apply lucas_primality 5435664887 (5 : ZMod 5435664887)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2717832443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2717832443, 1)] : List FactorBlock).map factorBlockValue).prod) = 5435664887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_2717832443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 5435664887) ^ 2717832443 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 5435664887) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5789622337 : Nat.Prime 5789622337 := by
  apply lucas_primality 5789622337 (10 : ZMod 5789622337)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (223, 1), (135221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (223, 1), (135221, 1)] : List FactorBlock).map factorBlockValue).prod) = 5789622337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_223
      · exact prime_eightySixCF_135221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5789622337) ^ 2894811168 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789622337) ^ 1929874112 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789622337) ^ 25962432 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5789622337) ^ 42816 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5864051159 : Nat.Prime 5864051159 := by
  apply lucas_primality 5864051159 (7 : ZMod 5864051159)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (41, 1), (444179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (41, 1), (444179, 1)] : List FactorBlock).map factorBlockValue).prod) = 5864051159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_444179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5864051159) ^ 2932025579 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5864051159) ^ 837721594 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5864051159) ^ 254958746 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5864051159) ^ 143025638 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5864051159) ^ 13202 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5881104239 : Nat.Prime 5881104239 := by
  apply lucas_primality 5881104239 (17 : ZMod 5881104239)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (43, 1), (3599207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (43, 1), (3599207, 1)] : List FactorBlock).map factorBlockValue).prod) = 5881104239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_3599207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 5881104239) ^ 2940552119 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 5881104239) ^ 309531802 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 5881104239) ^ 136769866 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 5881104239) ^ 1634 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6021419953 : Nat.Prime 6021419953 := by
  apply lucas_primality 6021419953 (5 : ZMod 6021419953)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (139, 1), (947, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (139, 1), (947, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 6021419953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_139
      · exact prime_eightySixCF_947
      · exact prime_eightySixCF_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6021419953) ^ 3010709976 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6021419953) ^ 2007139984 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6021419953) ^ 43319568 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6021419953) ^ 6358416 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6021419953) ^ 6318384 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6098397427 : Nat.Prime 6098397427 := by
  apply lucas_primality 6098397427 (3 : ZMod 6098397427)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (103, 1), (299029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (103, 1), (299029, 1)] : List FactorBlock).map factorBlockValue).prod) = 6098397427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_103
      · exact prime_eightySixCF_299029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6098397427) ^ 3049198713 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6098397427) ^ 2032799142 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6098397427) ^ 554399766 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6098397427) ^ 59207742 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6098397427) ^ 20394 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6264150371 : Nat.Prime 6264150371 := by
  apply lucas_primality 6264150371 (2 : ZMod 6264150371)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (139, 1), (63473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (139, 1), (63473, 1)] : List FactorBlock).map factorBlockValue).prod) = 6264150371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_71
      · exact prime_eightySixCF_139
      · exact prime_eightySixCF_63473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6264150371) ^ 3132075185 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264150371) ^ 1252830074 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264150371) ^ 88227470 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264150371) ^ 45065830 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264150371) ^ 98690 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6296388337 : Nat.Prime 6296388337 := by
  apply lucas_primality 6296388337 (10 : ZMod 6296388337)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (151, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (151, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) = 6296388337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_151
      · exact prime_eightySixCF_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6296388337) ^ 3148194168 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 6296388337) ^ 2098796112 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 6296388337) ^ 899484048 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 6296388337) ^ 41697936 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 6296388337) ^ 456624 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_7349874941 : Nat.Prime 7349874941 := by
  apply lucas_primality 7349874941 (2 : ZMod 7349874941)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (31, 1), (107, 1), (4817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (31, 1), (107, 1), (4817, 1)] : List FactorBlock).map factorBlockValue).prod) = 7349874941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_107
      · exact prime_eightySixCF_4817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7349874941) ^ 3674937470 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7349874941) ^ 1469974988 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7349874941) ^ 319559780 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7349874941) ^ 237092740 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7349874941) ^ 68690420 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7349874941) ^ 1525820 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_7536468637 : Nat.Prime 7536468637 := by
  apply lucas_primality 7536468637 (2 : ZMod 7536468637)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (277, 1), (13259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (277, 1), (13259, 1)] : List FactorBlock).map factorBlockValue).prod) = 7536468637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_277
      · exact prime_eightySixCF_13259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7536468637) ^ 3768234318 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7536468637) ^ 2512156212 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7536468637) ^ 396656244 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7536468637) ^ 27207468 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7536468637) ^ 568404 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_7911508541 : Nat.Prime 7911508541 := by
  apply lucas_primality 7911508541 (3 : ZMod 7911508541)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 2), (83, 1), (28201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 2), (83, 1), (28201, 1)] : List FactorBlock).map factorBlockValue).prod) = 7911508541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_83
      · exact prime_eightySixCF_28201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7911508541) ^ 3955754270 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7911508541) ^ 1582301708 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7911508541) ^ 608577580 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7911508541) ^ 95319380 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7911508541) ^ 280540 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_8761719101 : Nat.Prime 8761719101 := by
  apply lucas_primality 8761719101 (2 : ZMod 8761719101)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (2826361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (2826361, 1)] : List FactorBlock).map factorBlockValue).prod) = 8761719101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_2826361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8761719101) ^ 4380859550 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8761719101) ^ 1752343820 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8761719101) ^ 282636100 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8761719101) ^ 3100 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_8966799823 : Nat.Prime 8966799823 := by
  apply lucas_primality 8966799823 (6 : ZMod 8966799823)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (2617, 1), (9679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (2617, 1), (9679, 1)] : List FactorBlock).map factorBlockValue).prod) = 8966799823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_59
      · exact prime_eightySixCF_2617
      · exact prime_eightySixCF_9679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8966799823) ^ 4483399911 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8966799823) ^ 2988933274 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8966799823) ^ 151979658 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8966799823) ^ 3426366 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8966799823) ^ 926418 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_9344712709 : Nat.Prime 9344712709 := by
  apply lucas_primality 9344712709 (2 : ZMod 9344712709)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (89, 1), (101, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (89, 1), (101, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 9344712709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_67
      · exact prime_eightySixCF_89
      · exact prime_eightySixCF_101
      · exact prime_eightySixCF_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9344712709) ^ 4672356354 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9344712709) ^ 3114904236 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9344712709) ^ 139473324 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9344712709) ^ 104996772 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9344712709) ^ 92521908 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9344712709) ^ 21681468 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_10489453297 : Nat.Prime 10489453297 := by
  apply lucas_primality 10489453297 (10 : ZMod 10489453297)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (59, 1), (529129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (59, 1), (529129, 1)] : List FactorBlock).map factorBlockValue).prod) = 10489453297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_59
      · exact prime_eightySixCF_529129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10489453297) ^ 5244726648 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 10489453297) ^ 3496484432 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 10489453297) ^ 1498493328 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 10489453297) ^ 177787344 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 10489453297) ^ 19824 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_10836954251 : Nat.Prime 10836954251 := by
  apply lucas_primality 10836954251 (2 : ZMod 10836954251)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (113, 1), (383609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (113, 1), (383609, 1)] : List FactorBlock).map factorBlockValue).prod) = 10836954251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_113
      · exact prime_eightySixCF_383609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10836954251) ^ 5418477125 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10836954251) ^ 2167390850 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10836954251) ^ 95902250 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10836954251) ^ 28250 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_13176995179 : Nat.Prime 13176995179 := by
  apply lucas_primality 13176995179 (3 : ZMod 13176995179)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (115587677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (115587677, 1)] : List FactorBlock).map factorBlockValue).prod) = 13176995179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_115587677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13176995179) ^ 6588497589 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 13176995179) ^ 4392331726 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 13176995179) ^ 693526062 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 13176995179) ^ 114 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_13219889591 : Nat.Prime 13219889591 := by
  apply lucas_primality 13219889591 (17 : ZMod 13219889591)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (397, 1), (31121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (397, 1), (31121, 1)] : List FactorBlock).map factorBlockValue).prod) = 13219889591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_107
      · exact prime_eightySixCF_397
      · exact prime_eightySixCF_31121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 13219889591) ^ 6609944795 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 13219889591) ^ 2643977918 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 13219889591) ^ 123550370 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 13219889591) ^ 33299470 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 13219889591) ^ 424790 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_14709272621 : Nat.Prime 14709272621 := by
  apply lucas_primality 14709272621 (2 : ZMod 14709272621)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (105066233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (105066233, 1)] : List FactorBlock).map factorBlockValue).prod) = 14709272621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_105066233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14709272621) ^ 7354636310 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14709272621) ^ 2941854524 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14709272621) ^ 2101324660 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14709272621) ^ 140 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_14853170743 : Nat.Prime 14853170743 := by
  apply lucas_primality 14853170743 (3 : ZMod 14853170743)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (145619321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (145619321, 1)] : List FactorBlock).map factorBlockValue).prod) = 14853170743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_145619321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14853170743) ^ 7426585371 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14853170743) ^ 4951056914 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14853170743) ^ 873715926 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14853170743) ^ 102 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_15150595237 : Nat.Prime 15150595237 := by
  apply lucas_primality 15150595237 (2 : ZMod 15150595237)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (83, 1), (107, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (83, 1), (107, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 15150595237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_83
      · exact prime_eightySixCF_107
      · exact prime_eightySixCF_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15150595237) ^ 7575297618 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15150595237) ^ 5050198412 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15150595237) ^ 2164370748 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15150595237) ^ 658721532 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15150595237) ^ 182537292 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15150595237) ^ 141594348 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15150595237) ^ 17158092 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_15410509783 : Nat.Prime 15410509783 := by
  apply lucas_primality 15410509783 (5 : ZMod 15410509783)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12841, 1), (200017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12841, 1), (200017, 1)] : List FactorBlock).map factorBlockValue).prod) = 15410509783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_12841
      · exact prime_eightySixCF_200017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15410509783) ^ 7705254891 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 15410509783) ^ 5136836594 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 15410509783) ^ 1200102 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 15410509783) ^ 77046 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_19911391697 : Nat.Prime 19911391697 := by
  apply lucas_primality 19911391697 (3 : ZMod 19911391697)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (223, 1), (41959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (223, 1), (41959, 1)] : List FactorBlock).map factorBlockValue).prod) = 19911391697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_223
      · exact prime_eightySixCF_41959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19911391697) ^ 9955695848 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 19911391697) ^ 2844484528 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 19911391697) ^ 1047967984 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 19911391697) ^ 89288752 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 19911391697) ^ 474544 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_25393270657 : Nat.Prime 25393270657 := by
  apply lucas_primality 25393270657 (7 : ZMod 25393270657)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (5086793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (5086793, 1)] : List FactorBlock).map factorBlockValue).prod) = 25393270657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_5086793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 25393270657) ^ 12696635328 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 25393270657) ^ 8464423552 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 25393270657) ^ 1953328512 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 25393270657) ^ 4992 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_26777921921 : Nat.Prime 26777921921 := by
  apply lucas_primality 26777921921 (3 : ZMod 26777921921)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (181, 1), (271, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (181, 1), (271, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 26777921921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_181
      · exact prime_eightySixCF_271
      · exact prime_eightySixCF_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26777921921) ^ 13388960960 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 26777921921) ^ 5355584384 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 26777921921) ^ 147944320 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 26777921921) ^ 98811520 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 26777921921) ^ 31392640 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_29418545243 : Nat.Prime 29418545243 := by
  apply lucas_primality 29418545243 (2 : ZMod 29418545243)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14709272621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14709272621, 1)] : List FactorBlock).map factorBlockValue).prod) = 29418545243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_14709272621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29418545243) ^ 14709272621 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 29418545243) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_31438890289 : Nat.Prime 31438890289 := by
  apply lucas_primality 31438890289 (34 : ZMod 31438890289)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (13, 1), (1866031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (13, 1), (1866031, 1)] : List FactorBlock).map factorBlockValue).prod) = 31438890289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_1866031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (34 : ZMod 31438890289) ^ 15719445144 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (34 : ZMod 31438890289) ^ 10479630096 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (34 : ZMod 31438890289) ^ 2418376176 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (34 : ZMod 31438890289) ^ 16848 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_33770048863 : Nat.Prime 33770048863 := by
  apply lucas_primality 33770048863 (3 : ZMod 33770048863)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (199, 1), (111791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (199, 1), (111791, 1)] : List FactorBlock).map factorBlockValue).prod) = 33770048863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_199
      · exact prime_eightySixCF_111791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33770048863) ^ 16885024431 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33770048863) ^ 11256682954 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33770048863) ^ 3070004442 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33770048863) ^ 1468262994 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33770048863) ^ 169698738 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33770048863) ^ 302082 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_38965297807 : Nat.Prime 38965297807 := by
  apply lucas_primality 38965297807 (3 : ZMod 38965297807)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (359, 1), (2009971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (359, 1), (2009971, 1)] : List FactorBlock).map factorBlockValue).prod) = 38965297807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_359
      · exact prime_eightySixCF_2009971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38965297807) ^ 19482648903 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 38965297807) ^ 12988432602 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 38965297807) ^ 108538434 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 38965297807) ^ 19386 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_43631343577 : Nat.Prime 43631343577 := by
  apply lucas_primality 43631343577 (5 : ZMod 43631343577)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (19, 1), (31, 1), (342949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (19, 1), (31, 1), (342949, 1)] : List FactorBlock).map factorBlockValue).prod) = 43631343577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_342949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43631343577) ^ 21815671788 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 43631343577) ^ 14543781192 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 43631343577) ^ 2296386504 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 43631343577) ^ 1407462696 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 43631343577) ^ 127224 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_50392638631 : Nat.Prime 50392638631 := by
  apply lucas_primality 50392638631 (11 : ZMod 50392638631)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (61, 1), (9178987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (61, 1), (9178987, 1)] : List FactorBlock).map factorBlockValue).prod) = 50392638631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_61
      · exact prime_eightySixCF_9178987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 50392638631) ^ 25196319315 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 50392638631) ^ 16797546210 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 50392638631) ^ 10078527726 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 50392638631) ^ 826108830 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 50392638631) ^ 5490 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_50495222623 : Nat.Prime 50495222623 := by
  apply lucas_primality 50495222623 (3 : ZMod 50495222623)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (6763, 1), (95723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (6763, 1), (95723, 1)] : List FactorBlock).map factorBlockValue).prod) = 50495222623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_6763
      · exact prime_eightySixCF_95723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50495222623) ^ 25247611311 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 50495222623) ^ 16831740874 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 50495222623) ^ 3884247894 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 50495222623) ^ 7466394 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 50495222623) ^ 527514 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_60347928229 : Nat.Prime 60347928229 := by
  apply lucas_primality 60347928229 (2 : ZMod 60347928229)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (102632531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (102632531, 1)] : List FactorBlock).map factorBlockValue).prod) = 60347928229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_102632531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60347928229) ^ 30173964114 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60347928229) ^ 20115976076 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60347928229) ^ 8621132604 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 60347928229) ^ 588 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_99278801021 : Nat.Prime 99278801021 := by
  apply lucas_primality 99278801021 (2 : ZMod 99278801021)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (6379, 1), (15881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (6379, 1), (15881, 1)] : List FactorBlock).map factorBlockValue).prod) = 99278801021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_6379
      · exact prime_eightySixCF_15881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 99278801021) ^ 49639400510 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 99278801021) ^ 19855760204 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 99278801021) ^ 14182685860 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 99278801021) ^ 15563380 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 99278801021) ^ 6251420 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_115591328911 : Nat.Prime 115591328911 := by
  apply lucas_primality 115591328911 (6 : ZMod 115591328911)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (53, 1), (8077661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (53, 1), (8077661, 1)] : List FactorBlock).map factorBlockValue).prod) = 115591328911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_53
      · exact prime_eightySixCF_8077661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 115591328911) ^ 57795664455 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 115591328911) ^ 38530442970 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 115591328911) ^ 23118265782 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 115591328911) ^ 2180968470 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 115591328911) ^ 14310 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_119609102143 : Nat.Prime 119609102143 := by
  apply lucas_primality 119609102143 (3 : ZMod 119609102143)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (29, 1), (2521, 1), (10099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (29, 1), (2521, 1), (10099, 1)] : List FactorBlock).map factorBlockValue).prod) = 119609102143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_29
      · exact prime_eightySixCF_2521
      · exact prime_eightySixCF_10099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119609102143) ^ 59804551071 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 119609102143) ^ 39869700714 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 119609102143) ^ 4124451798 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 119609102143) ^ 47445102 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 119609102143) ^ 11843658 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_141670369109 : Nat.Prime 141670369109 := by
  apply lucas_primality 141670369109 (2 : ZMod 141670369109)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2083387781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2083387781, 1)] : List FactorBlock).map factorBlockValue).prod) = 141670369109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_2083387781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 141670369109) ^ 70835184554 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 141670369109) ^ 8333551124 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 141670369109) ^ 68 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_152062966837 : Nat.Prime 152062966837 := by
  apply lucas_primality 152062966837 (2 : ZMod 152062966837)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (19, 1), (113, 1), (178853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (19, 1), (113, 1), (178853, 1)] : List FactorBlock).map factorBlockValue).prod) = 152062966837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_113
      · exact prime_eightySixCF_178853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 152062966837) ^ 76031483418 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 152062966837) ^ 50687655612 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 152062966837) ^ 13823906076 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 152062966837) ^ 8003314044 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 152062966837) ^ 1345689972 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 152062966837) ^ 850212 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_161153077381 : Nat.Prime 161153077381 := by
  apply lucas_primality 161153077381 (2 : ZMod 161153077381)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5171, 1), (519413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5171, 1), (519413, 1)] : List FactorBlock).map factorBlockValue).prod) = 161153077381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_5171
      · exact prime_eightySixCF_519413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161153077381) ^ 80576538690 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 161153077381) ^ 53717692460 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 161153077381) ^ 32230615476 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 161153077381) ^ 31164780 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 161153077381) ^ 310260 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_179766767837 : Nat.Prime 179766767837 := by
  apply lucas_primality 179766767837 (2 : ZMod 179766767837)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (504962831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (504962831, 1)] : List FactorBlock).map factorBlockValue).prod) = 179766767837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_89
      · exact prime_eightySixCF_504962831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 179766767837) ^ 89883383918 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 179766767837) ^ 2019851324 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 179766767837) ^ 356 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_215771764693 : Nat.Prime 215771764693 := by
  apply lucas_primality 215771764693 (2 : ZMod 215771764693)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (37, 1), (2325227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (37, 1), (2325227, 1)] : List FactorBlock).map factorBlockValue).prod) = 215771764693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_2325227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 215771764693) ^ 107885882346 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 215771764693) ^ 71923921564 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 215771764693) ^ 19615614972 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 215771764693) ^ 11356408668 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 215771764693) ^ 5831669316 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 215771764693) ^ 92796 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_270294939917 : Nat.Prime 270294939917 := by
  apply lucas_primality 270294939917 (2 : ZMod 270294939917)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (3974925587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (3974925587, 1)] : List FactorBlock).map factorBlockValue).prod) = 270294939917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_3974925587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 270294939917) ^ 135147469958 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 270294939917) ^ 15899702348 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 270294939917) ^ 68 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_299770546373 : Nat.Prime 299770546373 := by
  apply lucas_primality 299770546373 (2 : ZMod 299770546373)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (61, 1), (1289, 1), (7877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (61, 1), (1289, 1), (7877, 1)] : List FactorBlock).map factorBlockValue).prod) = 299770546373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_61
      · exact prime_eightySixCF_1289
      · exact prime_eightySixCF_7877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 299770546373) ^ 149885273186 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 299770546373) ^ 27251867852 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 299770546373) ^ 4914271252 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 299770546373) ^ 232560548 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 299770546373) ^ 38056436 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_331155877183 : Nat.Prime 331155877183 := by
  apply lucas_primality 331155877183 (6 : ZMod 331155877183)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4245588169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4245588169, 1)] : List FactorBlock).map factorBlockValue).prod) = 331155877183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_4245588169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 331155877183) ^ 165577938591 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 331155877183) ^ 110385292394 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 331155877183) ^ 25473529014 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 331155877183) ^ 78 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_424019939659 : Nat.Prime 424019939659 := by
  apply lucas_primality 424019939659 (3 : ZMod 424019939659)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (193, 1), (52309393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (193, 1), (52309393, 1)] : List FactorBlock).map factorBlockValue).prod) = 424019939659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_193
      · exact prime_eightySixCF_52309393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 424019939659) ^ 212009969829 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 424019939659) ^ 141339979886 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 424019939659) ^ 60574277094 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 424019939659) ^ 2196994506 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 424019939659) ^ 8106 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_493496450119 : Nat.Prime 493496450119 := by
  apply lucas_primality 493496450119 (15 : ZMod 493496450119)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3916638493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3916638493, 1)] : List FactorBlock).map factorBlockValue).prod) = 493496450119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_3916638493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 493496450119) ^ 246748225059 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (15 : ZMod 493496450119) ^ 164498816706 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (15 : ZMod 493496450119) ^ 70499492874 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (15 : ZMod 493496450119) ^ 126 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_494116287107 : Nat.Prime 494116287107 := by
  apply lucas_primality 494116287107 (2 : ZMod 494116287107)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (1000235399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (1000235399, 1)] : List FactorBlock).map factorBlockValue).prod) = 494116287107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_1000235399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 494116287107) ^ 247058143553 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 494116287107) ^ 38008945162 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 494116287107) ^ 26006120374 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 494116287107) ^ 494 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_512506192909 : Nat.Prime 512506192909 := by
  apply lucas_primality 512506192909 (6 : ZMod 512506192909)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1301, 1), (32827709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1301, 1), (32827709, 1)] : List FactorBlock).map factorBlockValue).prod) = 512506192909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_1301
      · exact prime_eightySixCF_32827709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 512506192909) ^ 256253096454 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 512506192909) ^ 170835397636 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 512506192909) ^ 393932508 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 512506192909) ^ 15612 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_523792518911 : Nat.Prime 523792518911 := by
  apply lucas_primality 523792518911 (7 : ZMod 523792518911)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (607, 1), (2006791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (607, 1), (2006791, 1)] : List FactorBlock).map factorBlockValue).prod) = 523792518911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_607
      · exact prime_eightySixCF_2006791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 523792518911) ^ 261896259455 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 523792518911) ^ 104758503782 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 523792518911) ^ 12181221370 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 523792518911) ^ 862920130 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 523792518911) ^ 261010 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_599541092747 : Nat.Prime 599541092747 := by
  apply lucas_primality 599541092747 (2 : ZMod 599541092747)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (299770546373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (299770546373, 1)] : List FactorBlock).map factorBlockValue).prod) = 599541092747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_299770546373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 599541092747) ^ 299770546373 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 599541092747) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_674399034737 : Nat.Prime 674399034737 := by
  apply lucas_primality 674399034737 (3 : ZMod 674399034737)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (6021419953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (6021419953, 1)] : List FactorBlock).map factorBlockValue).prod) = 674399034737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_6021419953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 674399034737) ^ 337199517368 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 674399034737) ^ 96342719248 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 674399034737) ^ 112 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_781638030413 : Nat.Prime 781638030413 := by
  apply lucas_primality 781638030413 (2 : ZMod 781638030413)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6163, 1), (31706881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6163, 1), (31706881, 1)] : List FactorBlock).map factorBlockValue).prod) = 781638030413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_6163
      · exact prime_eightySixCF_31706881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 781638030413) ^ 390819015206 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 781638030413) ^ 126827524 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 781638030413) ^ 24652 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1047585037823 : Nat.Prime 1047585037823 := by
  apply lucas_primality 1047585037823 (5 : ZMod 1047585037823)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (523792518911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (523792518911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047585037823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_523792518911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1047585037823) ^ 523792518911 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047585037823) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1080184060313 : Nat.Prime 1080184060313 := by
  apply lucas_primality 1080184060313 (3 : ZMod 1080184060313)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (1015210583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (1015210583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080184060313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_1015210583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1080184060313) ^ 540092030156 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080184060313) ^ 154312008616 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080184060313) ^ 56851792648 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1080184060313) ^ 1064 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1434861692617 : Nat.Prime 1434861692617 := by
  apply lucas_primality 1434861692617 (5 : ZMod 1434861692617)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (494098379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (494098379, 1)] : List FactorBlock).map factorBlockValue).prod) = 1434861692617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_494098379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1434861692617) ^ 717430846308 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434861692617) ^ 478287230872 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434861692617) ^ 130441972056 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434861692617) ^ 2904 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1715398711337 : Nat.Prime 1715398711337 := by
  apply lucas_primality 1715398711337 (3 : ZMod 1715398711337)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (8431, 1), (285763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (8431, 1), (285763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1715398711337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_89
      · exact prime_eightySixCF_8431
      · exact prime_eightySixCF_285763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1715398711337) ^ 857699355668 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1715398711337) ^ 19274142824 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1715398711337) ^ 203463256 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1715398711337) ^ 6002872 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2025135185947 : Nat.Prime 2025135185947 := by
  apply lucas_primality 2025135185947 (5 : ZMod 2025135185947)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (19231, 1), (39089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (19231, 1), (39089, 1)] : List FactorBlock).map factorBlockValue).prod) = 2025135185947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_449
      · exact prime_eightySixCF_19231
      · exact prime_eightySixCF_39089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2025135185947) ^ 1012567592973 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2025135185947) ^ 675045061982 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2025135185947) ^ 4510323354 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2025135185947) ^ 105305766 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2025135185947) ^ 51808314 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2780064750499 : Nat.Prime 2780064750499 := by
  apply lucas_primality 2780064750499 (10 : ZMod 2780064750499)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (601, 1), (110136469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (601, 1), (110136469, 1)] : List FactorBlock).map factorBlockValue).prod) = 2780064750499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_601
      · exact prime_eightySixCF_110136469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2780064750499) ^ 1390032375249 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2780064750499) ^ 926688250166 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2780064750499) ^ 397152107214 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2780064750499) ^ 4625731698 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 2780064750499) ^ 25242 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5853625302691 : Nat.Prime 5853625302691 := by
  apply lucas_primality 5853625302691 (10 : ZMod 5853625302691)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (60103, 1), (98377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (60103, 1), (98377, 1)] : List FactorBlock).map factorBlockValue).prod) = 5853625302691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_60103
      · exact prime_eightySixCF_98377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5853625302691) ^ 2926812651345 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5853625302691) ^ 1951208434230 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5853625302691) ^ 1170725060538 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5853625302691) ^ 532147754790 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5853625302691) ^ 97393230 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 5853625302691) ^ 59501970 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_8234441369321 : Nat.Prime 8234441369321 := by
  apply lucas_primality 8234441369321 (3 : ZMod 8234441369321)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (61, 1), (251, 1), (277, 1), (48539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (61, 1), (251, 1), (277, 1), (48539, 1)] : List FactorBlock).map factorBlockValue).prod) = 8234441369321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_61
      · exact prime_eightySixCF_251
      · exact prime_eightySixCF_277
      · exact prime_eightySixCF_48539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8234441369321) ^ 4117220684660 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8234441369321) ^ 1646888273864 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8234441369321) ^ 134990842120 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8234441369321) ^ 32806539320 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8234441369321) ^ 29727225160 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8234441369321) ^ 169645880 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_8661059012653 : Nat.Prime 8661059012653 := by
  apply lucas_primality 8661059012653 (5 : ZMod 8661059012653)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (79, 1), (222832639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (79, 1), (222832639, 1)] : List FactorBlock).map factorBlockValue).prod) = 8661059012653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_79
      · exact prime_eightySixCF_222832639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8661059012653) ^ 4330529506326 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 8661059012653) ^ 2887019670884 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 8661059012653) ^ 211245341772 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 8661059012653) ^ 109633658388 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 8661059012653) ^ 38868 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_9176670773447 : Nat.Prime 9176670773447 := by
  apply lucas_primality 9176670773447 (5 : ZMod 9176670773447)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (23, 1), (1901, 1), (867281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (23, 1), (1901, 1), (867281, 1)] : List FactorBlock).map factorBlockValue).prod) = 9176670773447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_1901
      · exact prime_eightySixCF_867281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9176670773447) ^ 4588335386723 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 9176670773447) ^ 834242797586 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 9176670773447) ^ 398985685802 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 9176670773447) ^ 4827286046 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 9176670773447) ^ 10580966 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_12537454646291 : Nat.Prime 12537454646291 := by
  apply lucas_primality 12537454646291 (2 : ZMod 12537454646291)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (5231, 1), (34239437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (5231, 1), (34239437, 1)] : List FactorBlock).map factorBlockValue).prod) = 12537454646291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_5231
      · exact prime_eightySixCF_34239437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12537454646291) ^ 6268727323145 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12537454646291) ^ 2507490929258 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12537454646291) ^ 1791064949470 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12537454646291) ^ 2396760590 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12537454646291) ^ 366170 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_14164935458551 : Nat.Prime 14164935458551 := by
  apply lucas_primality 14164935458551 (3 : ZMod 14164935458551)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (347, 1), (272140931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (347, 1), (272140931, 1)] : List FactorBlock).map factorBlockValue).prod) = 14164935458551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_347
      · exact prime_eightySixCF_272140931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14164935458551) ^ 7082467729275 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14164935458551) ^ 4721645152850 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14164935458551) ^ 2832987091710 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14164935458551) ^ 40821139650 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 14164935458551) ^ 52050 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_14606487284791 : Nat.Prime 14606487284791 := by
  apply lucas_primality 14606487284791 (6 : ZMod 14606487284791)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (233, 1), (2089626221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (233, 1), (2089626221, 1)] : List FactorBlock).map factorBlockValue).prod) = 14606487284791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_233
      · exact prime_eightySixCF_2089626221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14606487284791) ^ 7303243642395 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14606487284791) ^ 4868829094930 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14606487284791) ^ 2921297456958 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14606487284791) ^ 62688786630 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14606487284791) ^ 6990 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_14617699037951 : Nat.Prime 14617699037951 := by
  apply lucas_primality 14617699037951 (7 : ZMod 14617699037951)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (839, 1), (348455281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (839, 1), (348455281, 1)] : List FactorBlock).map factorBlockValue).prod) = 14617699037951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_839
      · exact prime_eightySixCF_348455281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14617699037951) ^ 7308849518975 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 14617699037951) ^ 2923539807590 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 14617699037951) ^ 17422764050 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 14617699037951) ^ 41950 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_16245680277623 : Nat.Prime 16245680277623 := by
  apply lucas_primality 16245680277623 (5 : ZMod 16245680277623)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (61, 1), (5789622337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (61, 1), (5789622337, 1)] : List FactorBlock).map factorBlockValue).prod) = 16245680277623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_61
      · exact prime_eightySixCF_5789622337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16245680277623) ^ 8122840138811 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 16245680277623) ^ 706333925114 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 16245680277623) ^ 266322627502 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 16245680277623) ^ 2806 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_20405295982891 : Nat.Prime 20405295982891 := by
  apply lucas_primality 20405295982891 (3 : ZMod 20405295982891)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (13, 1), (131, 1), (223, 1), (28429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (13, 1), (131, 1), (223, 1), (28429, 1)] : List FactorBlock).map factorBlockValue).prod) = 20405295982891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_131
      · exact prime_eightySixCF_223
      · exact prime_eightySixCF_28429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20405295982891) ^ 10202647991445 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20405295982891) ^ 6801765327630 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20405295982891) ^ 4081059196578 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20405295982891) ^ 2915042283270 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20405295982891) ^ 1569638152530 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20405295982891) ^ 155765618190 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20405295982891) ^ 91503569430 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20405295982891) ^ 717763410 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_22208553183263 : Nat.Prime 22208553183263 := by
  apply lucas_primality 22208553183263 (5 : ZMod 22208553183263)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (389, 1), (224769277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (389, 1), (224769277, 1)] : List FactorBlock).map factorBlockValue).prod) = 22208553183263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_127
      · exact prime_eightySixCF_389
      · exact prime_eightySixCF_224769277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22208553183263) ^ 11104276591631 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 22208553183263) ^ 174870497506 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 22208553183263) ^ 57091396358 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 22208553183263) ^ 98806 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_23844733939571 : Nat.Prime 23844733939571 := by
  apply lucas_primality 23844733939571 (2 : ZMod 23844733939571)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (6098397427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (6098397427, 1)] : List FactorBlock).map factorBlockValue).prod) = 23844733939571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_6098397427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23844733939571) ^ 11922366969785 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23844733939571) ^ 4768946787914 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23844733939571) ^ 1402631408210 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23844733939571) ^ 1036727562590 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23844733939571) ^ 3910 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_25861916688493 : Nat.Prime 25861916688493 := by
  apply lucas_primality 25861916688493 (6 : ZMod 25861916688493)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4027, 1), (535177483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4027, 1), (535177483, 1)] : List FactorBlock).map factorBlockValue).prod) = 25861916688493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_4027
      · exact prime_eightySixCF_535177483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 25861916688493) ^ 12930958344246 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 25861916688493) ^ 8620638896164 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 25861916688493) ^ 6422129796 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 25861916688493) ^ 48324 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_26106798535723 : Nat.Prime 26106798535723 := by
  apply lucas_primality 26106798535723 (2 : ZMod 26106798535723)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (161153077381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (161153077381, 1)] : List FactorBlock).map factorBlockValue).prod) = 26106798535723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_161153077381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26106798535723) ^ 13053399267861 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 26106798535723) ^ 8702266178574 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 26106798535723) ^ 162 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_26650322031269 : Nat.Prime 26650322031269 := by
  apply lucas_primality 26650322031269 (2 : ZMod 26650322031269)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (512506192909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (512506192909, 1)] : List FactorBlock).map factorBlockValue).prod) = 26650322031269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_512506192909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26650322031269) ^ 13325161015634 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 26650322031269) ^ 2050024771636 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 26650322031269) ^ 52 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_27682457605529 : Nat.Prime 27682457605529 := by
  apply lucas_primality 27682457605529 (3 : ZMod 27682457605529)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (6329, 1), (4518499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (6329, 1), (4518499, 1)] : List FactorBlock).map factorBlockValue).prod) = 27682457605529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_6329
      · exact prime_eightySixCF_4518499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27682457605529) ^ 13841228802764 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27682457605529) ^ 2516587055048 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27682457605529) ^ 4373907032 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27682457605529) ^ 6126472 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_36677460114577 : Nat.Prime 36677460114577 := by
  apply lucas_primality 36677460114577 (5 : ZMod 36677460114577)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (223, 1), (5807, 1), (65563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (223, 1), (5807, 1), (65563, 1)] : List FactorBlock).map factorBlockValue).prod) = 36677460114577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_223
      · exact prime_eightySixCF_5807
      · exact prime_eightySixCF_65563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36677460114577) ^ 18338730057288 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 36677460114577) ^ 12225820038192 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 36677460114577) ^ 164472915312 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 36677460114577) ^ 6316077168 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 36677460114577) ^ 559423152 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_43721270003923 : Nat.Prime 43721270003923 := by
  apply lucas_primality 43721270003923 (3 : ZMod 43721270003923)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (13176995179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (13176995179, 1)] : List FactorBlock).map factorBlockValue).prod) = 43721270003923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_79
      · exact prime_eightySixCF_13176995179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43721270003923) ^ 21860635001961 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43721270003923) ^ 14573756667974 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43721270003923) ^ 6245895714846 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43721270003923) ^ 553433797518 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43721270003923) ^ 3318 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_44366040863279 : Nat.Prime 44366040863279 := by
  apply lucas_primality 44366040863279 (7 : ZMod 44366040863279)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (599541092747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (599541092747, 1)] : List FactorBlock).map factorBlockValue).prod) = 44366040863279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_599541092747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 44366040863279) ^ 22183020431639 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 44366040863279) ^ 1199082185494 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 44366040863279) ^ 74 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_55060024640683 : Nat.Prime 55060024640683 := by
  apply lucas_primality 55060024640683 (3 : ZMod 55060024640683)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9176670773447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9176670773447, 1)] : List FactorBlock).map factorBlockValue).prod) = 55060024640683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_9176670773447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55060024640683) ^ 27530012320341 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 55060024640683) ^ 18353341546894 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 55060024640683) ^ 6 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_55728471099661 : Nat.Prime 55728471099661 := by
  apply lucas_primality 55728471099661 (2 : ZMod 55728471099661)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (199, 1), (4667376139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (199, 1), (4667376139, 1)] : List FactorBlock).map factorBlockValue).prod) = 55728471099661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_199
      · exact prime_eightySixCF_4667376139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55728471099661) ^ 27864235549830 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55728471099661) ^ 18576157033220 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55728471099661) ^ 11145694219932 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55728471099661) ^ 280042568340 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55728471099661) ^ 11940 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_59001542835341 : Nat.Prime 59001542835341 := by
  apply lucas_primality 59001542835341 (2 : ZMod 59001542835341)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (47, 1), (8966799823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (47, 1), (8966799823, 1)] : List FactorBlock).map factorBlockValue).prod) = 59001542835341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_47
      · exact prime_eightySixCF_8966799823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59001542835341) ^ 29500771417670 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59001542835341) ^ 11800308567068 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59001542835341) ^ 8428791833620 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59001542835341) ^ 1255351975220 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59001542835341) ^ 6580 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_64768863132671 : Nat.Prime 64768863132671 := by
  apply lucas_primality 64768863132671 (11 : ZMod 64768863132671)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (3739, 1), (6991, 1), (7993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (3739, 1), (6991, 1), (7993, 1)] : List FactorBlock).map factorBlockValue).prod) = 64768863132671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_3739
      · exact prime_eightySixCF_6991
      · exact prime_eightySixCF_7993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 64768863132671) ^ 32384431566335 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 64768863132671) ^ 12953772626534 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 64768863132671) ^ 2089318165570 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 64768863132671) ^ 17322509530 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 64768863132671) ^ 9264606370 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 64768863132671) ^ 8103198190 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_82230831681221 : Nat.Prime 82230831681221 := by
  apply lucas_primality 82230831681221 (2 : ZMod 82230831681221)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (653, 1), (6296388337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (653, 1), (6296388337, 1)] : List FactorBlock).map factorBlockValue).prod) = 82230831681221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_653
      · exact prime_eightySixCF_6296388337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82230831681221) ^ 41115415840610 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 82230831681221) ^ 16446166336244 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 82230831681221) ^ 125927766740 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 82230831681221) ^ 13060 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_86702563279853 : Nat.Prime 86702563279853 := by
  apply lucas_primality 86702563279853 (5 : ZMod 86702563279853)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (89, 1), (2143, 1), (2357, 1), (3709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (89, 1), (2143, 1), (2357, 1), (3709, 1)] : List FactorBlock).map factorBlockValue).prod) = 86702563279853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_89
      · exact prime_eightySixCF_2143
      · exact prime_eightySixCF_2357
      · exact prime_eightySixCF_3709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 86702563279853) ^ 43351281639926 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 86702563279853) ^ 6669427944604 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 86702563279853) ^ 974186104268 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 86702563279853) ^ 40458498964 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 86702563279853) ^ 36785135036 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 86702563279853) ^ 23376264028 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_123136627768003 : Nat.Prime 123136627768003 := by
  apply lucas_primality 123136627768003 (3 : ZMod 123136627768003)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (229, 1), (161599, 1), (184859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (229, 1), (161599, 1), (184859, 1)] : List FactorBlock).map factorBlockValue).prod) = 123136627768003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_229
      · exact prime_eightySixCF_161599
      · exact prime_eightySixCF_184859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 123136627768003) ^ 61568313884001 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 123136627768003) ^ 41045542589334 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 123136627768003) ^ 537714531738 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 123136627768003) ^ 761988798 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 123136627768003) ^ 666111078 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_123140982875683 : Nat.Prime 123140982875683 := by
  apply lucas_primality 123140982875683 (2 : ZMod 123140982875683)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1080184060313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1080184060313, 1)] : List FactorBlock).map factorBlockValue).prod) = 123140982875683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_1080184060313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123140982875683) ^ 61570491437841 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 123140982875683) ^ 41046994291894 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 123140982875683) ^ 6481104361878 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 123140982875683) ^ 114 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_133429691622677 : Nat.Prime 133429691622677 := by
  apply lucas_primality 133429691622677 (2 : ZMod 133429691622677)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (93053, 1), (358477673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (93053, 1), (358477673, 1)] : List FactorBlock).map factorBlockValue).prod) = 133429691622677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_93053
      · exact prime_eightySixCF_358477673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 133429691622677) ^ 66714845811338 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 133429691622677) ^ 1433910692 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 133429691622677) ^ 372212 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_143068403637427 : Nat.Prime 143068403637427 := by
  apply lucas_primality 143068403637427 (2 : ZMod 143068403637427)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23844733939571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23844733939571, 1)] : List FactorBlock).map factorBlockValue).prod) = 143068403637427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_23844733939571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 143068403637427) ^ 71534201818713 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 143068403637427) ^ 47689467879142 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 143068403637427) ^ 6 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_151695347452669 : Nat.Prime 151695347452669 := by
  apply lucas_primality 151695347452669 (2 : ZMod 151695347452669)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (4027, 1), (36081961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (4027, 1), (36081961, 1)] : List FactorBlock).map factorBlockValue).prod) = 151695347452669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_29
      · exact prime_eightySixCF_4027
      · exact prime_eightySixCF_36081961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151695347452669) ^ 75847673726334 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 151695347452669) ^ 50565115817556 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 151695347452669) ^ 5230874050092 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 151695347452669) ^ 37669567284 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 151695347452669) ^ 4204188 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_155042133704539 : Nat.Prime 155042133704539 := by
  apply lucas_primality 155042133704539 (10 : ZMod 155042133704539)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (28571, 1), (8954713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (28571, 1), (8954713, 1)] : List FactorBlock).map factorBlockValue).prod) = 155042133704539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_101
      · exact prime_eightySixCF_28571
      · exact prime_eightySixCF_8954713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 155042133704539) ^ 77521066852269 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 155042133704539) ^ 51680711234846 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 155042133704539) ^ 1535070630738 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 155042133704539) ^ 5426556078 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 155042133704539) ^ 17314026 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_165778215570199 : Nat.Prime 165778215570199 := by
  apply lucas_primality 165778215570199 (3 : ZMod 165778215570199)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (119609102143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (119609102143, 1)] : List FactorBlock).map factorBlockValue).prod) = 165778215570199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_119609102143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 165778215570199) ^ 82889107785099 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 165778215570199) ^ 55259405190066 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 165778215570199) ^ 23682602224314 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 165778215570199) ^ 15070746870018 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 165778215570199) ^ 1386 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_192780426012613 : Nat.Prime 192780426012613 := by
  apply lucas_primality 192780426012613 (2 : ZMod 192780426012613)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (461, 1), (751, 1), (6173, 1), (7517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (461, 1), (751, 1), (6173, 1), (7517, 1)] : List FactorBlock).map factorBlockValue).prod) = 192780426012613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_461
      · exact prime_eightySixCF_751
      · exact prime_eightySixCF_6173
      · exact prime_eightySixCF_7517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 192780426012613) ^ 96390213006306 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 192780426012613) ^ 64260142004204 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 192780426012613) ^ 418178798292 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 192780426012613) ^ 256698303612 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 192780426012613) ^ 31229617044 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 192780426012613) ^ 25645926036 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_194666468652863 : Nat.Prime 194666468652863 := by
  apply lucas_primality 194666468652863 (5 : ZMod 194666468652863)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (67, 1), (8623, 1), (9910123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (67, 1), (8623, 1), (9910123, 1)] : List FactorBlock).map factorBlockValue).prod) = 194666468652863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_67
      · exact prime_eightySixCF_8623
      · exact prime_eightySixCF_9910123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 194666468652863) ^ 97333234326431 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 194666468652863) ^ 11450968744286 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 194666468652863) ^ 2905469681386 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 194666468652863) ^ 22575260194 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 194666468652863) ^ 19643194 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_229607543239909 : Nat.Prime 229607543239909 := by
  apply lucas_primality 229607543239909 (2 : ZMod 229607543239909)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21001, 1), (911097659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21001, 1), (911097659, 1)] : List FactorBlock).map factorBlockValue).prod) = 229607543239909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_21001
      · exact prime_eightySixCF_911097659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 229607543239909) ^ 114803771619954 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229607543239909) ^ 76535847746636 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229607543239909) ^ 10933171908 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229607543239909) ^ 252012 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_232918258347919 : Nat.Prime 232918258347919 := by
  apply lucas_primality 232918258347919 (6 : ZMod 232918258347919)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (11, 1), (13, 1), (19, 1), (457, 1), (128659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (11, 1), (13, 1), (19, 1), (457, 1), (128659, 1)] : List FactorBlock).map factorBlockValue).prod) = 232918258347919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_457
      · exact prime_eightySixCF_128659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 232918258347919) ^ 116459129173959 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 232918258347919) ^ 77639419449306 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 232918258347919) ^ 21174387122538 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 232918258347919) ^ 17916789103686 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 232918258347919) ^ 12258855702522 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 232918258347919) ^ 509667961374 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 232918258347919) ^ 1810353402 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_266099249068937 : Nat.Prime 266099249068937 := by
  apply lucas_primality 266099249068937 (3 : ZMod 266099249068937)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41719, 1), (797296343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41719, 1), (797296343, 1)] : List FactorBlock).map factorBlockValue).prod) = 266099249068937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_41719
      · exact prime_eightySixCF_797296343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 266099249068937) ^ 133049624534468 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 266099249068937) ^ 6378370744 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 266099249068937) ^ 333752 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_287789373714637 : Nat.Prime 287789373714637 := by
  apply lucas_primality 287789373714637 (2 : ZMod 287789373714637)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (27827, 1), (287280313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (27827, 1), (287280313, 1)] : List FactorBlock).map factorBlockValue).prod) = 287789373714637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_27827
      · exact prime_eightySixCF_287280313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 287789373714637) ^ 143894686857318 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 287789373714637) ^ 95929791238212 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 287789373714637) ^ 10342091268 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 287789373714637) ^ 1001772 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_293524314648701 : Nat.Prime 293524314648701 := by
  apply lucas_primality 293524314648701 (2 : ZMod 293524314648701)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (37, 1), (79841, 1), (993611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (37, 1), (79841, 1), (993611, 1)] : List FactorBlock).map factorBlockValue).prod) = 293524314648701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_79841
      · exact prime_eightySixCF_993611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 293524314648701) ^ 146762157324350 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 293524314648701) ^ 58704862929740 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 293524314648701) ^ 7933089585100 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 293524314648701) ^ 3676360700 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 293524314648701) ^ 295411700 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_448916511623603 : Nat.Prime 448916511623603 := by
  apply lucas_primality 448916511623603 (2 : ZMod 448916511623603)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (20405295982891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (20405295982891, 1)] : List FactorBlock).map factorBlockValue).prod) = 448916511623603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_20405295982891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 448916511623603) ^ 224458255811801 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 448916511623603) ^ 40810591965782 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 448916511623603) ^ 22 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_546679357593713 : Nat.Prime 546679357593713 := by
  apply lucas_primality 546679357593713 (3 : ZMod 546679357593713)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (25889, 1), (188538209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (25889, 1), (188538209, 1)] : List FactorBlock).map factorBlockValue).prod) = 546679357593713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_25889
      · exact prime_eightySixCF_188538209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 546679357593713) ^ 273339678796856 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 546679357593713) ^ 78097051084816 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 546679357593713) ^ 21116279408 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 546679357593713) ^ 2899568 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_606781389810677 : Nat.Prime 606781389810677 := by
  apply lucas_primality 606781389810677 (2 : ZMod 606781389810677)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151695347452669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151695347452669, 1)] : List FactorBlock).map factorBlockValue).prod) = 606781389810677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_151695347452669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 606781389810677) ^ 303390694905338 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 606781389810677) ^ 4 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_613071624046537 : Nat.Prime 613071624046537 := by
  apply lucas_primality 613071624046537 (7 : ZMod 613071624046537)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (181, 1), (223, 1), (23439739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (181, 1), (223, 1), (23439739, 1)] : List FactorBlock).map factorBlockValue).prod) = 613071624046537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_181
      · exact prime_eightySixCF_223
      · exact prime_eightySixCF_23439739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 613071624046537) ^ 306535812023268 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 613071624046537) ^ 204357208015512 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 613071624046537) ^ 3387136044456 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 613071624046537) ^ 2749200107832 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 613071624046537) ^ 26155224 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_654995336276321 : Nat.Prime 654995336276321 := by
  apply lucas_primality 654995336276321 (3 : ZMod 654995336276321)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (135661, 1), (2321239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (135661, 1), (2321239, 1)] : List FactorBlock).map factorBlockValue).prod) = 654995336276321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_135661
      · exact prime_eightySixCF_2321239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 654995336276321) ^ 327497668138160 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 654995336276321) ^ 130999067255264 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 654995336276321) ^ 50384256636640 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 654995336276321) ^ 4828177120 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 654995336276321) ^ 282174880 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_698979731564539 : Nat.Prime 698979731564539 := by
  apply lucas_primality 698979731564539 (2 : ZMod 698979731564539)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (127, 1), (4339, 1), (1381747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (127, 1), (4339, 1), (1381747, 1)] : List FactorBlock).map factorBlockValue).prod) = 698979731564539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_127
      · exact prime_eightySixCF_4339
      · exact prime_eightySixCF_1381747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 698979731564539) ^ 349489865782269 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 698979731564539) ^ 232993243854846 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 698979731564539) ^ 41116454797914 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 698979731564539) ^ 5503777413894 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 698979731564539) ^ 161092355742 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 698979731564539) ^ 505866654 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_988390983653951 : Nat.Prime 988390983653951 := by
  apply lucas_primality 988390983653951 (11 : ZMod 988390983653951)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (229, 1), (22159, 1), (205031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (229, 1), (22159, 1), (205031, 1)] : List FactorBlock).map factorBlockValue).prod) = 988390983653951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_229
      · exact prime_eightySixCF_22159
      · exact prime_eightySixCF_205031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 988390983653951) ^ 494195491826975 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 988390983653951) ^ 197678196730790 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 988390983653951) ^ 52020578087050 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 988390983653951) ^ 4316117832550 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 988390983653951) ^ 44604494050 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 988390983653951) ^ 4820690450 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1377363834279623 : Nat.Prime 1377363834279623 := by
  apply lucas_primality 1377363834279623 (5 : ZMod 1377363834279623)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (23, 1), (571, 1), (11093, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (23, 1), (571, 1), (11093, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1377363834279623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_571
      · exact prime_eightySixCF_11093
      · exact prime_eightySixCF_35543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1377363834279623) ^ 688681917139811 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1377363834279623) ^ 196766262039946 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1377363834279623) ^ 72492833383138 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1377363834279623) ^ 59885384099114 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1377363834279623) ^ 2412195856882 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1377363834279623) ^ 124165134254 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1377363834279623) ^ 38752042154 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1555173940816163 : Nat.Prime 1555173940816163 := by
  apply lucas_primality 1555173940816163 (2 : ZMod 1555173940816163)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (367, 1), (38501, 1), (1279801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (367, 1), (38501, 1), (1279801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1555173940816163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_367
      · exact prime_eightySixCF_38501
      · exact prime_eightySixCF_1279801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1555173940816163) ^ 777586970408081 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1555173940816163) ^ 36166835832934 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1555173940816163) ^ 4237531173886 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1555173940816163) ^ 40393079162 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1555173940816163) ^ 1215168562 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1967738311873079 : Nat.Prime 1967738311873079 := by
  apply lucas_primality 1967738311873079 (7 : ZMod 1967738311873079)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 2), (150209, 1), (3896491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 2), (150209, 1), (3896491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1967738311873079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_150209
      · exact prime_eightySixCF_3896491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1967738311873079) ^ 983869155936539 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1967738311873079) ^ 47993617362758 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1967738311873079) ^ 13100002742 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1967738311873079) ^ 505002658 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2754727668559247 : Nat.Prime 2754727668559247 := by
  apply lucas_primality 2754727668559247 (5 : ZMod 2754727668559247)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1377363834279623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1377363834279623, 1)] : List FactorBlock).map factorBlockValue).prod) = 2754727668559247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_1377363834279623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2754727668559247) ^ 1377363834279623 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2754727668559247) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_3137906321587649 : Nat.Prime 3137906321587649 := by
  apply lucas_primality 3137906321587649 (3 : ZMod 3137906321587649)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (41, 1), (6547, 1), (14050457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (41, 1), (6547, 1), (14050457, 1)] : List FactorBlock).map factorBlockValue).prod) = 3137906321587649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_6547
      · exact prime_eightySixCF_14050457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3137906321587649) ^ 1568953160793824 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137906321587649) ^ 241377409352896 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137906321587649) ^ 76534300526528 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137906321587649) ^ 479289189184 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3137906321587649) ^ 223331264 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5239962690210569 : Nat.Prime 5239962690210569 := by
  apply lucas_primality 5239962690210569 (3 : ZMod 5239962690210569)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (654995336276321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (654995336276321, 1)] : List FactorBlock).map factorBlockValue).prod) = 5239962690210569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_654995336276321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5239962690210569) ^ 2619981345105284 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5239962690210569) ^ 8 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6130716240465371 : Nat.Prime 6130716240465371 := by
  apply lucas_primality 6130716240465371 (2 : ZMod 6130716240465371)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (613071624046537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (613071624046537, 1)] : List FactorBlock).map factorBlockValue).prod) = 6130716240465371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_613071624046537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6130716240465371) ^ 3065358120232685 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6130716240465371) ^ 1226143248093074 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6130716240465371) ^ 10 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6173400588129287 : Nat.Prime 6173400588129287 := by
  apply lucas_primality 6173400588129287 (5 : ZMod 6173400588129287)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61253, 1), (50392638631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61253, 1), (50392638631, 1)] : List FactorBlock).map factorBlockValue).prod) = 6173400588129287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_61253
      · exact prime_eightySixCF_50392638631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6173400588129287) ^ 3086700294064643 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6173400588129287) ^ 100785277262 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6173400588129287) ^ 122506 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6253045835585099 : Nat.Prime 6253045835585099 := by
  apply lucas_primality 6253045835585099 (2 : ZMod 6253045835585099)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (165367, 1), (1718779177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (165367, 1), (1718779177, 1)] : List FactorBlock).map factorBlockValue).prod) = 6253045835585099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_165367
      · exact prime_eightySixCF_1718779177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6253045835585099) ^ 3126522917792549 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6253045835585099) ^ 568458712325918 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6253045835585099) ^ 37813141894 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6253045835585099) ^ 3638074 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_10498305615374749 : Nat.Prime 10498305615374749 := by
  apply lucas_primality 10498305615374749 (6 : ZMod 10498305615374749)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (211, 1), (5711, 1), (726011249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (211, 1), (5711, 1), (726011249, 1)] : List FactorBlock).map factorBlockValue).prod) = 10498305615374749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_211
      · exact prime_eightySixCF_5711
      · exact prime_eightySixCF_726011249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10498305615374749) ^ 5249152807687374 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10498305615374749) ^ 3499435205124916 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10498305615374749) ^ 49755002916468 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10498305615374749) ^ 1838260482468 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10498305615374749) ^ 14460252 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_12930700814475523 : Nat.Prime 12930700814475523 := by
  apply lucas_primality 12930700814475523 (3 : ZMod 12930700814475523)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (165778215570199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (165778215570199, 1)] : List FactorBlock).map factorBlockValue).prod) = 12930700814475523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_165778215570199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12930700814475523) ^ 6465350407237761 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 12930700814475523) ^ 4310233604825174 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 12930700814475523) ^ 994669293421194 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 12930700814475523) ^ 78 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_13465663324388183 : Nat.Prime 13465663324388183 := by
  apply lucas_primality 13465663324388183 (5 : ZMod 13465663324388183)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (80819, 1), (2251554997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (80819, 1), (2251554997, 1)] : List FactorBlock).map factorBlockValue).prod) = 13465663324388183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_80819
      · exact prime_eightySixCF_2251554997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13465663324388183) ^ 6732831662194091 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 13465663324388183) ^ 363936846605086 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 13465663324388183) ^ 166615069778 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 13465663324388183) ^ 5980606 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_22420586277429581 : Nat.Prime 22420586277429581 := by
  apply lucas_primality 22420586277429581 (3 : ZMod 22420586277429581)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (59001542835341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (59001542835341, 1)] : List FactorBlock).map factorBlockValue).prod) = 22420586277429581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_59001542835341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22420586277429581) ^ 11210293138714790 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 22420586277429581) ^ 4484117255485916 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 22420586277429581) ^ 1180030856706820 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 22420586277429581) ^ 380 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_24930448444664771 : Nat.Prime 24930448444664771 := by
  apply lucas_primality 24930448444664771 (2 : ZMod 24930448444664771)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (683, 1), (937, 1), (3001, 1), (185441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (683, 1), (937, 1), (3001, 1), (185441, 1)] : List FactorBlock).map factorBlockValue).prod) = 24930448444664771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_683
      · exact prime_eightySixCF_937
      · exact prime_eightySixCF_3001
      · exact prime_eightySixCF_185441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24930448444664771) ^ 12465224222332385 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930448444664771) ^ 4986089688932954 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930448444664771) ^ 3561492634952110 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930448444664771) ^ 36501388645190 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930448444664771) ^ 26606668564210 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930448444664771) ^ 8307380354770 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930448444664771) ^ 134438707970 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_29148006092387153 : Nat.Prime 29148006092387153 := by
  apply lucas_primality 29148006092387153 (3 : ZMod 29148006092387153)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (47, 1), (1047585037823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (47, 1), (1047585037823, 1)] : List FactorBlock).map factorBlockValue).prod) = 29148006092387153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_47
      · exact prime_eightySixCF_1047585037823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29148006092387153) ^ 14574003046193576 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29148006092387153) ^ 787783948442896 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29148006092387153) ^ 620170342391216 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29148006092387153) ^ 27824 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_31685840967107443 : Nat.Prime 31685840967107443 := by
  apply lucas_primality 31685840967107443 (2 : ZMod 31685840967107443)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (229607543239909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (229607543239909, 1)] : List FactorBlock).map factorBlockValue).prod) = 31685840967107443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_229607543239909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31685840967107443) ^ 15842920483553721 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31685840967107443) ^ 10561946989035814 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31685840967107443) ^ 1377645259439454 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31685840967107443) ^ 138 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_36275299710345517 : Nat.Prime 36275299710345517 := by
  apply lucas_primality 36275299710345517 (6 : ZMod 36275299710345517)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4363, 1), (55639, 1), (12452749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4363, 1), (55639, 1), (12452749, 1)] : List FactorBlock).map factorBlockValue).prod) = 36275299710345517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_4363
      · exact prime_eightySixCF_55639
      · exact prime_eightySixCF_12452749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 36275299710345517) ^ 18137649855172758 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 36275299710345517) ^ 12091766570115172 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 36275299710345517) ^ 8314302019332 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 36275299710345517) ^ 651976126644 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 36275299710345517) ^ 2913035484 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_47107389151914029 : Nat.Prime 47107389151914029 := by
  apply lucas_primality 47107389151914029 (2 : ZMod 47107389151914029)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (1201, 1), (37339, 1), (5359537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (1201, 1), (37339, 1), (5359537, 1)] : List FactorBlock).map factorBlockValue).prod) = 47107389151914029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_1201
      · exact prime_eightySixCF_37339
      · exact prime_eightySixCF_5359537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47107389151914029) ^ 23553694575957014 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47107389151914029) ^ 6729627021702004 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47107389151914029) ^ 39223471400428 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47107389151914029) ^ 1261613571652 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47107389151914029) ^ 8789451244 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_48121848266257231 : Nat.Prime 48121848266257231 := by
  apply lucas_primality 48121848266257231 (6 : ZMod 48121848266257231)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1552541, 1), (1033184701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1552541, 1), (1033184701, 1)] : List FactorBlock).map factorBlockValue).prod) = 48121848266257231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_1552541
      · exact prime_eightySixCF_1033184701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 48121848266257231) ^ 24060924133128615 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 48121848266257231) ^ 16040616088752410 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 48121848266257231) ^ 9624369653251446 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 48121848266257231) ^ 30995541030 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 48121848266257231) ^ 46576230 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_51964110565327039 : Nat.Prime 51964110565327039 := by
  apply lucas_primality 51964110565327039 (6 : ZMod 51964110565327039)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (199, 1), (82483, 1), (40587413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (199, 1), (82483, 1), (40587413, 1)] : List FactorBlock).map factorBlockValue).prod) = 51964110565327039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_199
      · exact prime_eightySixCF_82483
      · exact prime_eightySixCF_40587413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 51964110565327039) ^ 25982055282663519 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 51964110565327039) ^ 17321370188442346 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 51964110565327039) ^ 3997239274255926 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 51964110565327039) ^ 261126183745362 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 51964110565327039) ^ 629997824586 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 51964110565327039) ^ 1280301126 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_52615523762625797 : Nat.Prime 52615523762625797 := by
  apply lucas_primality 52615523762625797 (2 : ZMod 52615523762625797)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (43, 1), (107, 1), (1171, 1), (15164179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (43, 1), (107, 1), (1171, 1), (15164179, 1)] : List FactorBlock).map factorBlockValue).prod) = 52615523762625797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_107
      · exact prime_eightySixCF_1171
      · exact prime_eightySixCF_15164179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52615523762625797) ^ 26307761881312898 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 52615523762625797) ^ 7516503394660828 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 52615523762625797) ^ 2287631467940252 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 52615523762625797) ^ 1223616831688972 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 52615523762625797) ^ 491733866940428 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 52615523762625797) ^ 44932129600876 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 52615523762625797) ^ 3469724524 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_58296012184774307 : Nat.Prime 58296012184774307 := by
  apply lucas_primality 58296012184774307 (2 : ZMod 58296012184774307)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29148006092387153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29148006092387153, 1)] : List FactorBlock).map factorBlockValue).prod) = 58296012184774307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_29148006092387153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 58296012184774307) ^ 29148006092387153 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58296012184774307) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_78832641543957383 : Nat.Prime 78832641543957383 := by
  apply lucas_primality 78832641543957383 (5 : ZMod 78832641543957383)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (827, 1), (63409, 1), (751656937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (827, 1), (63409, 1), (751656937, 1)] : List FactorBlock).map factorBlockValue).prod) = 78832641543957383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_827
      · exact prime_eightySixCF_63409
      · exact prime_eightySixCF_751656937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 78832641543957383) ^ 39416320771978691 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 78832641543957383) ^ 95323629436466 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 78832641543957383) ^ 1243240573798 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 78832641543957383) ^ 104878486 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_94020637446457721 : Nat.Prime 94020637446457721 := by
  apply lucas_primality 94020637446457721 (11 : ZMod 94020637446457721)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (375233, 1), (6264150371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (375233, 1), (6264150371, 1)] : List FactorBlock).map factorBlockValue).prod) = 94020637446457721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_375233
      · exact prime_eightySixCF_6264150371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 94020637446457721) ^ 47010318723228860 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 94020637446457721) ^ 18804127489291544 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 94020637446457721) ^ 250566014840 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 94020637446457721) ^ 15009320 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_152551645182749623 : Nat.Prime 152551645182749623 := by
  apply lucas_primality 152551645182749623 (13 : ZMod 152551645182749623)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (31, 1), (2423, 1), (19911391697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (31, 1), (2423, 1), (19911391697, 1)] : List FactorBlock).map factorBlockValue).prod) = 152551645182749623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_2423
      · exact prime_eightySixCF_19911391697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 152551645182749623) ^ 76275822591374811 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 152551645182749623) ^ 50850548394249874 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 152551645182749623) ^ 8973626187220566 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 152551645182749623) ^ 4921020812346762 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 152551645182749623) ^ 62959820545914 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 152551645182749623) ^ 7661526 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_155893468657663103 : Nat.Prime 155893468657663103 := by
  apply lucas_primality 155893468657663103 (5 : ZMod 155893468657663103)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (728537, 1), (1753947043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (728537, 1), (1753947043, 1)] : List FactorBlock).map factorBlockValue).prod) = 155893468657663103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_61
      · exact prime_eightySixCF_728537
      · exact prime_eightySixCF_1753947043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 155893468657663103) ^ 77946734328831551 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 155893468657663103) ^ 2555630633732182 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 155893468657663103) ^ 213981539246 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 155893468657663103) ^ 88881514 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_319446204823247071 : Nat.Prime 319446204823247071 := by
  apply lucas_primality 319446204823247071 (3 : ZMod 319446204823247071)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (287789373714637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (287789373714637, 1)] : List FactorBlock).map factorBlockValue).prod) = 319446204823247071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_287789373714637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 319446204823247071) ^ 159723102411623535 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 319446204823247071) ^ 106482068274415690 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 319446204823247071) ^ 63889240964649414 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 319446204823247071) ^ 8633681211439110 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 319446204823247071) ^ 1110 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_350107246434092759 : Nat.Prime 350107246434092759 := by
  apply lucas_primality 350107246434092759 (17 : ZMod 350107246434092759)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (13465663324388183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (13465663324388183, 1)] : List FactorBlock).map factorBlockValue).prod) = 350107246434092759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_13465663324388183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 350107246434092759) ^ 175053623217046379 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 350107246434092759) ^ 26931326648776366 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (17 : ZMod 350107246434092759) ^ 26 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_387452095336285321 : Nat.Prime 387452095336285321 := by
  apply lucas_primality 387452095336285321 (7 : ZMod 387452095336285321)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (293524314648701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (293524314648701, 1)] : List FactorBlock).map factorBlockValue).prod) = 387452095336285321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_293524314648701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 387452095336285321) ^ 193726047668142660 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 387452095336285321) ^ 129150698445428440 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 387452095336285321) ^ 77490419067257064 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 387452095336285321) ^ 35222917757844120 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 387452095336285321) ^ 1320 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_519587627612798447 : Nat.Prime 519587627612798447 := by
  apply lucas_primality 519587627612798447 (5 : ZMod 519587627612798447)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (37, 1), (691, 1), (781638030413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (37, 1), (691, 1), (781638030413, 1)] : List FactorBlock).map factorBlockValue).prod) = 519587627612798447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_691
      · exact prime_eightySixCF_781638030413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 519587627612798447) ^ 259793813806399223 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 519587627612798447) ^ 39968279047138342 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 519587627612798447) ^ 14042908854399958 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 519587627612798447) ^ 751935785257306 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 519587627612798447) ^ 664742 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_591867139869379259 : Nat.Prime 591867139869379259 := by
  apply lucas_primality 591867139869379259 (2 : ZMod 591867139869379259)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (32607563, 1), (477663757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (32607563, 1), (477663757, 1)] : List FactorBlock).map factorBlockValue).prod) = 591867139869379259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_32607563
      · exact prime_eightySixCF_477663757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 591867139869379259) ^ 295933569934689629 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591867139869379259) ^ 31150902098388382 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591867139869379259) ^ 18151222766 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 591867139869379259) ^ 1239087394 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_915309871096497739 : Nat.Prime 915309871096497739 := by
  apply lucas_primality 915309871096497739 (3 : ZMod 915309871096497739)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (152551645182749623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (152551645182749623, 1)] : List FactorBlock).map factorBlockValue).prod) = 915309871096497739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_152551645182749623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 915309871096497739) ^ 457654935548248869 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 915309871096497739) ^ 305103290365499246 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 915309871096497739) ^ 6 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1444319920914839987 : Nat.Prime 1444319920914839987 := by
  apply lucas_primality 1444319920914839987 (2 : ZMod 1444319920914839987)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (1967738311873079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (1967738311873079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1444319920914839987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_367
      · exact prime_eightySixCF_1967738311873079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1444319920914839987) ^ 722159960457419993 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444319920914839987) ^ 3935476623746158 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444319920914839987) ^ 734 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_2236984761816209413 : Nat.Prime 2236984761816209413 := by
  apply lucas_primality 2236984761816209413 (2 : ZMod 2236984761816209413)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (62659, 1), (141670369109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (62659, 1), (141670369109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2236984761816209413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_62659
      · exact prime_eightySixCF_141670369109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2236984761816209413) ^ 1118492380908104706 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2236984761816209413) ^ 745661587272069804 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2236984761816209413) ^ 319569251688029916 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2236984761816209413) ^ 35700933015468 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2236984761816209413) ^ 15790068 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_4956577692484363229 : Nat.Prime 4956577692484363229 := by
  apply lucas_primality 4956577692484363229 (2 : ZMod 4956577692484363229)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2922373, 1), (424019939659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2922373, 1), (424019939659, 1)] : List FactorBlock).map factorBlockValue).prod) = 4956577692484363229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_2922373
      · exact prime_eightySixCF_424019939659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4956577692484363229) ^ 2478288846242181614 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4956577692484363229) ^ 1696079758636 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4956577692484363229) ^ 11689492 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5532534115644437119 : Nat.Prime 5532534115644437119 := by
  apply lucas_primality 5532534115644437119 (3 : ZMod 5532534115644437119)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (19, 1), (17553637, 1), (131653631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (19, 1), (17553637, 1), (131653631, 1)] : List FactorBlock).map factorBlockValue).prod) = 5532534115644437119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_17553637
      · exact prime_eightySixCF_131653631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5532534115644437119) ^ 2766267057822218559 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5532534115644437119) ^ 1844178038548145706 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5532534115644437119) ^ 790362016520633874 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5532534115644437119) ^ 291186006086549322 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5532534115644437119) ^ 315178792614 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5532534115644437119) ^ 42023406978 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_6625040987876854381 : Nat.Prime 6625040987876854381 := by
  apply lucas_primality 6625040987876854381 (2 : ZMod 6625040987876854381)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (71, 1), (1555173940816163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (71, 1), (1555173940816163, 1)] : List FactorBlock).map factorBlockValue).prod) = 6625040987876854381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_71
      · exact prime_eightySixCF_1555173940816163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6625040987876854381) ^ 3312520493938427190 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625040987876854381) ^ 2208346995958951460 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625040987876854381) ^ 1325008197575370876 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625040987876854381) ^ 93310436448969780 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625040987876854381) ^ 4260 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_8689302311277267319 : Nat.Prime 8689302311277267319 := by
  apply lucas_primality 8689302311277267319 (6 : ZMod 8689302311277267319)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (787, 1), (72467, 1), (25393270657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (787, 1), (72467, 1), (25393270657, 1)] : List FactorBlock).map factorBlockValue).prod) = 8689302311277267319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_787
      · exact prime_eightySixCF_72467
      · exact prime_eightySixCF_25393270657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8689302311277267319) ^ 4344651155638633659 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8689302311277267319) ^ 2896434103759089106 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8689302311277267319) ^ 11041044868204914 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8689302311277267319) ^ 119907024042354 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 8689302311277267319) ^ 342189174 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_8844962788948462711 : Nat.Prime 8844962788948462711 := by
  apply lucas_primality 8844962788948462711 (3 : ZMod 8844962788948462711)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 3), (1351099, 1), (3166183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 3), (1351099, 1), (3166183, 1)] : List FactorBlock).map factorBlockValue).prod) = 8844962788948462711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_1351099
      · exact prime_eightySixCF_3166183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8844962788948462711) ^ 4422481394474231355 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8844962788948462711) ^ 2948320929649487570 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8844962788948462711) ^ 1768992557789692542 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8844962788948462711) ^ 215730799730450310 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8844962788948462711) ^ 6546494956290 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8844962788948462711) ^ 2793572825370 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_9913155384968726459 : Nat.Prime 9913155384968726459 := by
  apply lucas_primality 9913155384968726459 (2 : ZMod 9913155384968726459)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4956577692484363229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4956577692484363229, 1)] : List FactorBlock).map factorBlockValue).prod) = 9913155384968726459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_4956577692484363229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9913155384968726459) ^ 4956577692484363229 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9913155384968726459) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_23019135744881434919 : Nat.Prime 23019135744881434919 := by
  apply lucas_primality 23019135744881434919 (13 : ZMod 23019135744881434919)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (239, 1), (38069, 1), (29418545243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (239, 1), (38069, 1), (29418545243, 1)] : List FactorBlock).map factorBlockValue).prod) = 23019135744881434919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_43
      · exact prime_eightySixCF_239
      · exact prime_eightySixCF_38069
      · exact prime_eightySixCF_29418545243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 23019135744881434919) ^ 11509567872440717459 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 23019135744881434919) ^ 535328738253056626 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 23019135744881434919) ^ 96314375501595962 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 23019135744881434919) ^ 604668778924622 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (13 : ZMod 23019135744881434919) ^ 782470226 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_29480699004321004519 : Nat.Prime 29480699004321004519 := by
  apply lucas_primality 29480699004321004519 (7 : ZMod 29480699004321004519)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (41, 1), (59657597, 1), (154523153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (41, 1), (59657597, 1), (154523153, 1)] : List FactorBlock).map factorBlockValue).prod) = 29480699004321004519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_59657597
      · exact prime_eightySixCF_154523153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 29480699004321004519) ^ 14740349502160502259 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 29480699004321004519) ^ 9826899668107001506 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 29480699004321004519) ^ 2267746077255461886 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 29480699004321004519) ^ 719041439129780598 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 29480699004321004519) ^ 494165043294 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 29480699004321004519) ^ 190784995206 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_59525976160792063841 : Nat.Prime 59525976160792063841 := by
  apply lucas_primality 59525976160792063841 (3 : ZMod 59525976160792063841)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (71, 1), (5239962690210569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (71, 1), (5239962690210569, 1)] : List FactorBlock).map factorBlockValue).prod) = 59525976160792063841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_71
      · exact prime_eightySixCF_5239962690210569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59525976160792063841) ^ 29762988080396031920 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 59525976160792063841) ^ 11905195232158412768 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 59525976160792063841) ^ 838394030433691040 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 59525976160792063841) ^ 11360 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_86773828379402302771 : Nat.Prime 86773828379402302771 := by
  apply lucas_primality 86773828379402302771 (10 : ZMod 86773828379402302771)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (275749447, 1), (10489453297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (275749447, 1), (10489453297, 1)] : List FactorBlock).map factorBlockValue).prod) = 86773828379402302771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_275749447
      · exact prime_eightySixCF_10489453297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 86773828379402302771) ^ 43386914189701151385 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 86773828379402302771) ^ 28924609459800767590 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 86773828379402302771) ^ 17354765675880460554 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 86773828379402302771) ^ 314683598910 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 86773828379402302771) ^ 8272483410 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_94528956537205044931 : Nat.Prime 94528956537205044931 := by
  apply lucas_primality 94528956537205044931 (2 : ZMod 94528956537205044931)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (350107246434092759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (350107246434092759, 1)] : List FactorBlock).map factorBlockValue).prod) = 94528956537205044931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_350107246434092759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94528956537205044931) ^ 47264478268602522465 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94528956537205044931) ^ 31509652179068348310 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94528956537205044931) ^ 18905791307441008986 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94528956537205044931) ^ 270 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_136007726907724033553 : Nat.Prime 136007726907724033553 := by
  apply lucas_primality 136007726907724033553 (3 : ZMod 136007726907724033553)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (751, 1), (769, 1), (261619, 1), (56261077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (751, 1), (769, 1), (261619, 1), (56261077, 1)] : List FactorBlock).map factorBlockValue).prod) = 136007726907724033553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_751
      · exact prime_eightySixCF_769
      · exact prime_eightySixCF_261619
      · exact prime_eightySixCF_56261077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 136007726907724033553) ^ 68003863453862016776 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 136007726907724033553) ^ 181102166321869552 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 136007726907724033553) ^ 176863103911214608 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 136007726907724033553) ^ 519869454847408 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 136007726907724033553) ^ 2417439092176 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_149965267751556007691 : Nat.Prime 149965267751556007691 := by
  apply lucas_primality 149965267751556007691 (6 : ZMod 149965267751556007691)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (5623, 1), (43721270003923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (5623, 1), (43721270003923, 1)] : List FactorBlock).map factorBlockValue).prod) = 149965267751556007691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_61
      · exact prime_eightySixCF_5623
      · exact prime_eightySixCF_43721270003923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 149965267751556007691) ^ 74982633875778003845 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 149965267751556007691) ^ 29993053550311201538 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 149965267751556007691) ^ 2458447012320590290 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 149965267751556007691) ^ 26669974702393030 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 149965267751556007691) ^ 3430030 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_153335198581199446243 : Nat.Prime 153335198581199446243 := by
  apply lucas_primality 153335198581199446243 (2 : ZMod 153335198581199446243)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 3), (3064561, 1), (1697366299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 3), (3064561, 1), (1697366299, 1)] : List FactorBlock).map factorBlockValue).prod) = 153335198581199446243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_3064561
      · exact prime_eightySixCF_1697366299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153335198581199446243) ^ 76667599290599723121 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 153335198581199446243) ^ 51111732860399815414 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 153335198581199446243) ^ 9019717563599967426 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 153335198581199446243) ^ 50034963761922 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 153335198581199446243) ^ 90337129158 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_185221680321024209803 : Nat.Prime 185221680321024209803 := by
  apply lucas_primality 185221680321024209803 (2 : ZMod 185221680321024209803)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (37, 1), (36275299710345517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (37, 1), (36275299710345517, 1)] : List FactorBlock).map factorBlockValue).prod) = 185221680321024209803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_36275299710345517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 185221680321024209803) ^ 92610840160512104901 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 185221680321024209803) ^ 61740560107008069934 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 185221680321024209803) ^ 8053116535696704774 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 185221680321024209803) ^ 5005991360027681346 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 185221680321024209803) ^ 5106 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_319581976182978859489 : Nat.Prime 319581976182978859489 := by
  apply lucas_primality 319581976182978859489 (11 : ZMod 319581976182978859489)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (181, 1), (6130716240465371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (181, 1), (6130716240465371, 1)] : List FactorBlock).map factorBlockValue).prod) = 319581976182978859489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_181
      · exact prime_eightySixCF_6130716240465371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 319581976182978859489) ^ 159790988091489429744 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 319581976182978859489) ^ 106527325394326286496 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 319581976182978859489) ^ 1765646277254026848 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 319581976182978859489) ^ 52128 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_323149452545771238703 : Nat.Prime 323149452545771238703 := by
  apply lucas_primality 323149452545771238703 (3 : ZMod 323149452545771238703)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (6779, 1), (27682457605529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (6779, 1), (27682457605529, 1)] : List FactorBlock).map factorBlockValue).prod) = 323149452545771238703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_6779
      · exact prime_eightySixCF_27682457605529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 323149452545771238703) ^ 161574726272885619351 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 323149452545771238703) ^ 107716484181923746234 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 323149452545771238703) ^ 46164207506538748386 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 323149452545771238703) ^ 7881693964531005822 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 323149452545771238703) ^ 47669191996720938 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 323149452545771238703) ^ 11673438 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_473713395013476018683 : Nat.Prime 473713395013476018683 := by
  apply lucas_primality 473713395013476018683 (2 : ZMod 473713395013476018683)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (239, 1), (58296012184774307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (239, 1), (58296012184774307, 1)] : List FactorBlock).map factorBlockValue).prod) = 473713395013476018683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_239
      · exact prime_eightySixCF_58296012184774307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 473713395013476018683) ^ 236856697506738009341 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 473713395013476018683) ^ 27865493824322118746 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 473713395013476018683) ^ 1982064414282326438 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 473713395013476018683) ^ 8126 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_7004273041388899288459 : Nat.Prime 7004273041388899288459 := by
  apply lucas_primality 7004273041388899288459 (2 : ZMod 7004273041388899288459)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (113, 2), (691, 1), (1780001, 1), (24776239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (113, 2), (691, 1), (1780001, 1), (24776239, 1)] : List FactorBlock).map factorBlockValue).prod) = 7004273041388899288459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_113
      · exact prime_eightySixCF_691
      · exact prime_eightySixCF_1780001
      · exact prime_eightySixCF_24776239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7004273041388899288459) ^ 3502136520694449644229 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7004273041388899288459) ^ 2334757680462966429486 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7004273041388899288459) ^ 61984717180432737066 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7004273041388899288459) ^ 10136429871763964238 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7004273041388899288459) ^ 3934982644048458 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7004273041388899288459) ^ 282701221980822 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_7344417253017097811863 : Nat.Prime 7344417253017097811863 := by
  apply lucas_primality 7344417253017097811863 (3 : ZMod 7344417253017097811863)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (136007726907724033553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (136007726907724033553, 1)] : List FactorBlock).map factorBlockValue).prod) = 7344417253017097811863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_136007726907724033553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7344417253017097811863) ^ 3672208626508548905931 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7344417253017097811863) ^ 2448139084339032603954 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7344417253017097811863) ^ 54 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_8680697460782116517339 : Nat.Prime 8680697460782116517339 := by
  apply lucas_primality 8680697460782116517339 (2 : ZMod 8680697460782116517339)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (443, 1), (2399, 1), (1237471, 1), (3300316727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (443, 1), (2399, 1), (1237471, 1), (3300316727, 1)] : List FactorBlock).map factorBlockValue).prod) = 8680697460782116517339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_443
      · exact prime_eightySixCF_2399
      · exact prime_eightySixCF_1237471
      · exact prime_eightySixCF_3300316727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8680697460782116517339) ^ 4340348730391058258669 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8680697460782116517339) ^ 19595253861810646766 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8680697460782116517339) ^ 3618464969062991462 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8680697460782116517339) ^ 7014869407672678 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8680697460782116517339) ^ 2630261935094 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_9826362229489105794911 : Nat.Prime 9826362229489105794911 := by
  apply lucas_primality 9826362229489105794911 (21 : ZMod 9826362229489105794911)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (17, 2), (23, 1), (4517, 1), (738197, 1), (3410369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (17, 2), (23, 1), (4517, 1), (738197, 1), (3410369, 1)] : List FactorBlock).map factorBlockValue).prod) = 9826362229489105794911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_4517
      · exact prime_eightySixCF_738197
      · exact prime_eightySixCF_3410369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 9826362229489105794911) ^ 4913181114744552897455 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (21 : ZMod 9826362229489105794911) ^ 1965272445897821158982 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (21 : ZMod 9826362229489105794911) ^ 755874017653008138070 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (21 : ZMod 9826362229489105794911) ^ 578021307617006223230 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (21 : ZMod 9826362229489105794911) ^ 427233140412569817170 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (21 : ZMod 9826362229489105794911) ^ 2175417805952868230 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (21 : ZMod 9826362229489105794911) ^ 13311300681917030 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (21 : ZMod 9826362229489105794911) ^ 2881319361479390 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_10751791643539973198071 : Nat.Prime 10751791643539973198071 := by
  apply lucas_primality 10751791643539973198071 (6 : ZMod 10751791643539973198071)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (4021, 1), (50929, 1), (60347928229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (4021, 1), (50929, 1), (60347928229, 1)] : List FactorBlock).map factorBlockValue).prod) = 10751791643539973198071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_29
      · exact prime_eightySixCF_4021
      · exact prime_eightySixCF_50929
      · exact prime_eightySixCF_60347928229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10751791643539973198071) ^ 5375895821769986599035 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10751791643539973198071) ^ 3583930547846657732690 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10751791643539973198071) ^ 2150358328707994639614 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10751791643539973198071) ^ 370751435984137006830 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10751791643539973198071) ^ 2673909883994024670 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10751791643539973198071) ^ 211113346885663830 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 10751791643539973198071) ^ 178163392830 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_19884133584839184445247 : Nat.Prime 19884133584839184445247 := by
  apply lucas_primality 19884133584839184445247 (5 : ZMod 19884133584839184445247)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (59, 1), (199, 1), (367, 1), (588257, 1), (2996393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (59, 1), (199, 1), (367, 1), (588257, 1), (2996393, 1)] : List FactorBlock).map factorBlockValue).prod) = 19884133584839184445247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_59
      · exact prime_eightySixCF_199
      · exact prime_eightySixCF_367
      · exact prime_eightySixCF_588257
      · exact prime_eightySixCF_2996393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19884133584839184445247) ^ 9942066792419592222623 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 2840590512119883492178 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 1807648507712653131386 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 1169654916755246143838 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 337019213302359058394 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 99920269270548665554 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 54180200503649003938 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 33801779808551678 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 19884133584839184445247) ^ 6636023240222222 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_46147505075589229326533 : Nat.Prime 46147505075589229326533 := by
  apply lucas_primality 46147505075589229326533 (3 : ZMod 46147505075589229326533)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (1181, 1), (48121848266257231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (1181, 1), (48121848266257231, 1)] : List FactorBlock).map factorBlockValue).prod) = 46147505075589229326533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_29
      · exact prime_eightySixCF_1181
      · exact prime_eightySixCF_48121848266257231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46147505075589229326533) ^ 23073752537794614663266 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 46147505075589229326533) ^ 6592500725084175618076 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 46147505075589229326533) ^ 1591293278468594114708 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 46147505075589229326533) ^ 39074940792200871572 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 46147505075589229326533) ^ 958972 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_74834618199995823395353 : Nat.Prime 74834618199995823395353 := by
  apply lucas_primality 74834618199995823395353 (5 : ZMod 74834618199995823395353)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (310443967, 1), (1434861692617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (310443967, 1), (1434861692617, 1)] : List FactorBlock).map factorBlockValue).prod) = 74834618199995823395353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_310443967
      · exact prime_eightySixCF_1434861692617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74834618199995823395353) ^ 37417309099997911697676 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 74834618199995823395353) ^ 24944872733331941131784 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 74834618199995823395353) ^ 10690659742856546199336 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 74834618199995823395353) ^ 241056764359656 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 74834618199995823395353) ^ 52154586456 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_160413093742257767682883 : Nat.Prime 160413093742257767682883 := by
  apply lucas_primality 160413093742257767682883 (12 : ZMod 160413093742257767682883)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (19, 1), (23, 1), (37, 1), (163, 1), (86702563279853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (19, 1), (23, 1), (37, 1), (163, 1), (86702563279853, 1)] : List FactorBlock).map factorBlockValue).prod) = 160413093742257767682883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_37
      · exact prime_eightySixCF_163
      · exact prime_eightySixCF_86702563279853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 160413093742257767682883) ^ 80206546871128883841441 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (12 : ZMod 160413093742257767682883) ^ 53471031247419255894294 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (12 : ZMod 160413093742257767682883) ^ 12339468749404443667914 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (12 : ZMod 160413093742257767682883) ^ 8442794407487250930678 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (12 : ZMod 160413093742257767682883) ^ 6974482336619902942734 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (12 : ZMod 160413093742257767682883) ^ 4335489020061020748186 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (12 : ZMod 160413093742257767682883) ^ 984129409461704096214 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (12 : ZMod 160413093742257767682883) ^ 1850153994 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_172231758810787591864283 : Nat.Prime 172231758810787591864283 := by
  apply lucas_primality 172231758810787591864283 (2 : ZMod 172231758810787591864283)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (911, 1), (94528956537205044931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (911, 1), (94528956537205044931, 1)] : List FactorBlock).map factorBlockValue).prod) = 172231758810787591864283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_911
      · exact prime_eightySixCF_94528956537205044931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 172231758810787591864283) ^ 86115879405393795932141 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 172231758810787591864283) ^ 189057913074410089862 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 172231758810787591864283) ^ 1822 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_436455605491349119172621 : Nat.Prime 436455605491349119172621 := by
  apply lucas_primality 436455605491349119172621 (3 : ZMod 436455605491349119172621)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1637, 1), (69151, 1), (192780426012613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1637, 1), (69151, 1), (192780426012613, 1)] : List FactorBlock).map factorBlockValue).prod) = 436455605491349119172621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_1637
      · exact prime_eightySixCF_69151
      · exact prime_eightySixCF_192780426012613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 436455605491349119172621) ^ 218227802745674559586310 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436455605491349119172621) ^ 87291121098269823834524 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436455605491349119172621) ^ 266619184783964031260 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436455605491349119172621) ^ 6311631147652949620 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 436455605491349119172621) ^ 2264003740 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_569250397693563284695189 : Nat.Prime 569250397693563284695189 := by
  apply lucas_primality 569250397693563284695189 (2 : ZMod 569250397693563284695189)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (15410509783, 1), (38965297807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (15410509783, 1), (38965297807, 1)] : List FactorBlock).map factorBlockValue).prod) = 569250397693563284695189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_79
      · exact prime_eightySixCF_15410509783
      · exact prime_eightySixCF_38965297807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 569250397693563284695189) ^ 284625198846781642347594 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 569250397693563284695189) ^ 189750132564521094898396 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 569250397693563284695189) ^ 7205701236627383350572 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 569250397693563284695189) ^ 36939102321036 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 569250397693563284695189) ^ 14609163274284 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_574350389393889741653639 : Nat.Prime 574350389393889741653639 := by
  apply lucas_primality 574350389393889741653639 (11 : ZMod 574350389393889741653639)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (7004273041388899288459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (7004273041388899288459, 1)] : List FactorBlock).map factorBlockValue).prod) = 574350389393889741653639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_7004273041388899288459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 574350389393889741653639) ^ 287175194696944870826819 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 574350389393889741653639) ^ 14008546082777798576918 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 574350389393889741653639) ^ 82 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_717141954554604560693317 : Nat.Prime 717141954554604560693317 := by
  apply lucas_primality 717141954554604560693317 (2 : ZMod 717141954554604560693317)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (319581976182978859489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (319581976182978859489, 1)] : List FactorBlock).map factorBlockValue).prod) = 717141954554604560693317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_319581976182978859489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 717141954554604560693317) ^ 358570977277302280346658 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 717141954554604560693317) ^ 239047318184868186897772 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 717141954554604560693317) ^ 65194723141327687335756 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 717141954554604560693317) ^ 42184820856153209452548 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 717141954554604560693317) ^ 2244 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_1327020086830195191871169 : Nat.Prime 1327020086830195191871169 := by
  apply lucas_primality 1327020086830195191871169 (3 : ZMod 1327020086830195191871169)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (17, 1), (15973, 1), (1512209, 1), (50495222623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (17, 1), (15973, 1), (1512209, 1), (50495222623, 1)] : List FactorBlock).map factorBlockValue).prod) = 1327020086830195191871169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_17
      · exact prime_eightySixCF_15973
      · exact prime_eightySixCF_1512209
      · exact prime_eightySixCF_50495222623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1327020086830195191871169) ^ 663510043415097595935584 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327020086830195191871169) ^ 78060005107658540698304 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327020086830195191871169) ^ 83078951156964577216 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327020086830195191871169) ^ 877537487761410752 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1327020086830195191871169) ^ 26280111620416 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5763886169662286020747001 : Nat.Prime 5763886169662286020747001 := by
  apply lucas_primality 5763886169662286020747001 (3 : ZMod 5763886169662286020747001)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (7, 1), (31, 1), (2451028841, 1), (10836954251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (7, 1), (31, 1), (2451028841, 1), (10836954251, 1)] : List FactorBlock).map factorBlockValue).prod) = 5763886169662286020747001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_2451028841
      · exact prime_eightySixCF_10836954251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5763886169662286020747001) ^ 2881943084831143010373500 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5763886169662286020747001) ^ 1152777233932457204149400 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5763886169662286020747001) ^ 823412309951755145821000 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5763886169662286020747001) ^ 185931811924589871637000 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5763886169662286020747001) ^ 2351619072467000 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5763886169662286020747001) ^ 531873258497000 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_16681698446733835177354733 : Nat.Prime 16681698446733835177354733 := by
  apply lucas_primality 16681698446733835177354733 (2 : ZMod 16681698446733835177354733)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (45545387, 1), (698979731564539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (45545387, 1), (698979731564539, 1)] : List FactorBlock).map factorBlockValue).prod) = 16681698446733835177354733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_131
      · exact prime_eightySixCF_45545387
      · exact prime_eightySixCF_698979731564539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16681698446733835177354733) ^ 8340849223366917588677366 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16681698446733835177354733) ^ 127341209517052176926372 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16681698446733835177354733) ^ 366265379339818436 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16681698446733835177354733) ^ 23865782788 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_26700355050641472007872137 : Nat.Prime 26700355050641472007872137 := by
  apply lucas_primality 26700355050641472007872137 (3 : ZMod 26700355050641472007872137)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1955370029, 1), (55060024640683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1955370029, 1), (55060024640683, 1)] : List FactorBlock).map factorBlockValue).prod) = 26700355050641472007872137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_1955370029
      · exact prime_eightySixCF_55060024640683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26700355050641472007872137) ^ 13350177525320736003936068 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 26700355050641472007872137) ^ 861301775827144258318456 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 26700355050641472007872137) ^ 13654886110889384 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 26700355050641472007872137) ^ 484931767192 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_66280933528580655414587417 : Nat.Prime 66280933528580655414587417 := by
  apply lucas_primality 66280933528580655414587417 (3 : ZMod 66280933528580655414587417)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (9199, 1), (53309, 1), (449263, 1), (1979261701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (9199, 1), (53309, 1), (449263, 1), (1979261701, 1)] : List FactorBlock).map factorBlockValue).prod) = 66280933528580655414587417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_9199
      · exact prime_eightySixCF_53309
      · exact prime_eightySixCF_449263
      · exact prime_eightySixCF_1979261701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66280933528580655414587417) ^ 33140466764290327707293708 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66280933528580655414587417) ^ 3488470185714771337609864 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66280933528580655414587417) ^ 7205232474027682945384 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66280933528580655414587417) ^ 1243334775152050412024 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66280933528580655414587417) ^ 147532588992595997032 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66280933528580655414587417) ^ 33487705792060216 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_75259031852585288975556697 : Nat.Prime 75259031852585288975556697 := by
  apply lucas_primality 75259031852585288975556697 (10 : ZMod 75259031852585288975556697)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (271, 1), (91243, 1), (606781389810677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (271, 1), (91243, 1), (606781389810677, 1)] : List FactorBlock).map factorBlockValue).prod) = 75259031852585288975556697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_11
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_271
      · exact prime_eightySixCF_91243
      · exact prime_eightySixCF_606781389810677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 75259031852585288975556697) ^ 37629515926292644487778348 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 75259031852585288975556697) ^ 25086343950861762991852232 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 75259031852585288975556697) ^ 6841730168416844452323336 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 75259031852585288975556697) ^ 3961001676451857314502984 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 75259031852585288975556697) ^ 277708604622085937179176 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 75259031852585288975556697) ^ 824819787299686430472 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (10 : ZMod 75259031852585288975556697) ^ 124029894648 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_95649061178591463222932359 : Nat.Prime 95649061178591463222932359 := by
  apply lucas_primality 95649061178591463222932359 (6 : ZMod 95649061178591463222932359)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (31, 1), (69991, 1), (319446204823247071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (31, 1), (69991, 1), (319446204823247071, 1)] : List FactorBlock).map factorBlockValue).prod) = 95649061178591463222932359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_69991
      · exact prime_eightySixCF_319446204823247071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 95649061178591463222932359) ^ 47824530589295731611466179 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95649061178591463222932359) ^ 31883020392863821074310786 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95649061178591463222932359) ^ 4158654833851802748823146 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95649061178591463222932359) ^ 3085453586406176232997818 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95649061178591463222932359) ^ 1366590864233850969738 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95649061178591463222932359) ^ 299421498 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_135566602710456967207969463 : Nat.Prime 135566602710456967207969463 := by
  apply lucas_primality 135566602710456967207969463 (5 : ZMod 135566602710456967207969463)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (463, 1), (46861, 1), (213887, 1), (14606487284791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (463, 1), (46861, 1), (213887, 1), (14606487284791, 1)] : List FactorBlock).map factorBlockValue).prod) = 135566602710456967207969463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_463
      · exact prime_eightySixCF_46861
      · exact prime_eightySixCF_213887
      · exact prime_eightySixCF_14606487284791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 135566602710456967207969463) ^ 67783301355228483603984731 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135566602710456967207969463) ^ 292800437819561484250474 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135566602710456967207969463) ^ 2892951552686817763342 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135566602710456967207969463) ^ 633823480204299313226 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135566602710456967207969463) ^ 9281259762682 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_262725974245071641875909813 : Nat.Prime 262725974245071641875909813 := by
  apply lucas_primality 262725974245071641875909813 (2 : ZMod 262725974245071641875909813)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (2689, 1), (155723, 1), (24999179, 1), (90933649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (2689, 1), (155723, 1), (24999179, 1), (90933649, 1)] : List FactorBlock).map factorBlockValue).prod) = 262725974245071641875909813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_23
      · exact prime_eightySixCF_2689
      · exact prime_eightySixCF_155723
      · exact prime_eightySixCF_24999179
      · exact prime_eightySixCF_90933649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 262725974245071641875909813) ^ 131362987122535820937954906 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 262725974245071641875909813) ^ 87575324748357213958636604 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 262725974245071641875909813) ^ 11422868445437897472865644 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 262725974245071641875909813) ^ 97703969596530919254708 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 262725974245071641875909813) ^ 1687136609525064646044 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 262725974245071641875909813) ^ 10509384097976643228 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 262725974245071641875909813) ^ 2889205229684246388 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_271133205420913934415938927 : Nat.Prime 271133205420913934415938927 := by
  apply lucas_primality 271133205420913934415938927 (5 : ZMod 271133205420913934415938927)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (135566602710456967207969463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (135566602710456967207969463, 1)] : List FactorBlock).map factorBlockValue).prod) = 271133205420913934415938927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_135566602710456967207969463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 271133205420913934415938927) ^ 135566602710456967207969463 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (5 : ZMod 271133205420913934415938927) ^ 2 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_275541875427758063430832243 : Nat.Prime 275541875427758063430832243 := by
  apply lucas_primality 275541875427758063430832243 (2 : ZMod 275541875427758063430832243)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (267763, 1), (5532534115644437119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (267763, 1), (5532534115644437119, 1)] : List FactorBlock).map factorBlockValue).prod) = 275541875427758063430832243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_267763
      · exact prime_eightySixCF_5532534115644437119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 275541875427758063430832243) ^ 137770937713879031715416121 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 275541875427758063430832243) ^ 91847291809252687810277414 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 275541875427758063430832243) ^ 8888447594443808497768782 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 275541875427758063430832243) ^ 1029051345509865304134 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 275541875427758063430832243) ^ 49803918 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_568016491803590644726129037 : Nat.Prime 568016491803590644726129037 := by
  apply lucas_primality 568016491803590644726129037 (2 : ZMod 568016491803590644726129037)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (13, 1), (809, 1), (1215283, 1), (3783119, 1), (59935699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (13, 1), (809, 1), (1215283, 1), (3783119, 1), (59935699, 1)] : List FactorBlock).map factorBlockValue).prod) = 568016491803590644726129037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_809
      · exact prime_eightySixCF_1215283
      · exact prime_eightySixCF_3783119
      · exact prime_eightySixCF_59935699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 568016491803590644726129037) ^ 284008245901795322363064518 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 568016491803590644726129037) ^ 81145213114798663532304148 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 568016491803590644726129037) ^ 43693576292583895748163772 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 568016491803590644726129037) ^ 702121745121867298796204 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 568016491803590644726129037) ^ 467394419080650881092 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 568016491803590644726129037) ^ 150145023670571992244 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 568016491803590644726129037) ^ 9477097978011245764 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_716020788963681164830824631 : Nat.Prime 716020788963681164830824631 := by
  apply lucas_primality 716020788963681164830824631 (7 : ZMod 716020788963681164830824631)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (1109, 1), (190730851, 1), (12537454646291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (1109, 1), (190730851, 1), (12537454646291, 1)] : List FactorBlock).map factorBlockValue).prod) = 716020788963681164830824631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_1109
      · exact prime_eightySixCF_190730851
      · exact prime_eightySixCF_12537454646291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 716020788963681164830824631) ^ 358010394481840582415412315 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 716020788963681164830824631) ^ 238673596321227054943608210 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 716020788963681164830824631) ^ 143204157792736232966164926 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 716020788963681164830824631) ^ 645645436396466334383070 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 716020788963681164830824631) ^ 3754090044738914130 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (7 : ZMod 716020788963681164830824631) ^ 57110538714930 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_3389165067761424180199236587 : Nat.Prime 3389165067761424180199236587 := by
  apply lucas_primality 3389165067761424180199236587 (2 : ZMod 3389165067761424180199236587)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36721, 1), (46147505075589229326533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36721, 1), (46147505075589229326533, 1)] : List FactorBlock).map factorBlockValue).prod) = 3389165067761424180199236587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_36721
      · exact prime_eightySixCF_46147505075589229326533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3389165067761424180199236587) ^ 1694582533880712090099618293 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3389165067761424180199236587) ^ 92295010151178458653066 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3389165067761424180199236587) ^ 73442 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_5648608446269040300332060983 : Nat.Prime 5648608446269040300332060983 := by
  apply lucas_primality 5648608446269040300332060983 (6 : ZMod 5648608446269040300332060983)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (719, 1), (436455605491349119172621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (719, 1), (436455605491349119172621, 1)] : List FactorBlock).map factorBlockValue).prod) = 5648608446269040300332060983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_719
      · exact prime_eightySixCF_436455605491349119172621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5648608446269040300332060983) ^ 2824304223134520150166030491 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5648608446269040300332060983) ^ 1882869482089680100110686994 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5648608446269040300332060983) ^ 7856200898844284145107178 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5648608446269040300332060983) ^ 12942 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_14524993147548960772282442519 : Nat.Prime 14524993147548960772282442519 := by
  apply lucas_primality 14524993147548960772282442519 (11 : ZMod 14524993147548960772282442519)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (41, 1), (717141954554604560693317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (41, 1), (717141954554604560693317, 1)] : List FactorBlock).map factorBlockValue).prod) = 14524993147548960772282442519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_13
      · exact prime_eightySixCF_19
      · exact prime_eightySixCF_41
      · exact prime_eightySixCF_717141954554604560693317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14524993147548960772282442519) ^ 7262496573774480386141221259 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 14524993147548960772282442519) ^ 1117307165196073905560187886 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 14524993147548960772282442519) ^ 764473323555208461699075922 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 14524993147548960772282442519) ^ 354268125549974652982498598 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (11 : ZMod 14524993147548960772282442519) ^ 20254 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_101674952032842725405977097609 : Nat.Prime 101674952032842725405977097609 := by
  apply lucas_primality 101674952032842725405977097609 (3 : ZMod 101674952032842725405977097609)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (283856533, 1), (1444319920914839987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (283856533, 1), (1444319920914839987, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_31
      · exact prime_eightySixCF_283856533
      · exact prime_eightySixCF_1444319920914839987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101674952032842725405977097609) ^ 50837476016421362702988548804 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 101674952032842725405977097609) ^ 3279837162349765335676680568 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 101674952032842725405977097609) ^ 358191340386880316776 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (3 : ZMod 101674952032842725405977097609) ^ 70396420184 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_101674952032842725405977097641 : Nat.Prime 101674952032842725405977097641 := by
  apply lucas_primality 101674952032842725405977097641 (26 : ZMod 101674952032842725405977097641)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 2), (5763886169662286020747001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 2), (5763886169662286020747001, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_3
      · exact prime_eightySixCF_5
      · exact prime_eightySixCF_7
      · exact prime_eightySixCF_5763886169662286020747001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 101674952032842725405977097641) ^ 50837476016421362702988548820 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (26 : ZMod 101674952032842725405977097641) ^ 33891650677614241801992365880 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (26 : ZMod 101674952032842725405977097641) ^ 20334990406568545081195419528 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (26 : ZMod 101674952032842725405977097641) ^ 14524993147548960772282442520 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (26 : ZMod 101674952032842725405977097641) ^ 17640 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem prime_eightySixCF_101674952032842725405977097699 : Nat.Prime 101674952032842725405977097699 := by
  apply lucas_primality 101674952032842725405977097699 (2 : ZMod 101674952032842725405977097699)
  · rw [← eightySixCFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (14461, 1), (537281, 1), (78832641543957383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (14461, 1), (537281, 1), (78832641543957383, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightySixCF_2
      · exact prime_eightySixCF_83
      · exact prime_eightySixCF_14461
      · exact prime_eightySixCF_537281
      · exact prime_eightySixCF_78832641543957383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101674952032842725405977097699) ^ 50837476016421362702988548849 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 101674952032842725405977097699) ^ 1224999422082442474770808406 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 101674952032842725405977097699) ^ 7030976559908908471473418 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 101674952032842725405977097699) ^ 189239805674949840783458 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide
    · change (2 : ZMod 101674952032842725405977097699) ^ 1289757009806 ≠ 1
      rw [← eightySixCFFastPow_eq_pow]
      decide

private theorem phi_eightySixCF_101674952032842725405977097600 : Nat.totient 101674952032842725405977097600 = 37538583886889720733678796800 := by
  rw [← show ((([(2, 7), (5, 2), (13, 1), (12821, 1), (4296829, 1), (44366040863279, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_5, prime_eightySixCF_13, prime_eightySixCF_12821, prime_eightySixCF_4296829, prime_eightySixCF_44366040863279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097601 : Nat.totient 101674952032842725405977097601 = 67780172865123106409824320960 := by
  rw [← show ((([(3, 1), (24133, 1), (211979, 1), (6625040987876854381, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_24133, prime_eightySixCF_211979, prime_eightySixCF_6625040987876854381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097602 : Nat.totient 101674952032842725405977097602 = 50121455227457681538157724100 := by
  rw [← show ((([(2, 1), (71, 1), (716020788963681164830824631, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_71, prime_eightySixCF_716020788963681164830824631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097603 : Nat.totient 101674952032842725405977097603 = 101673691475766096724117109568 := by
  rw [← show ((([(80713, 1), (119991719, 1), (10498305615374749, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_80713, prime_eightySixCF_119991719, prime_eightySixCF_10498305615374749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097604 : Nat.totient 101674952032842725405977097604 = 33891650671379190205410805872 := by
  rw [← show ((([(2, 2), (3, 2), (5435664887, 1), (519587627612798447, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_5435664887, prime_eightySixCF_519587627612798447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097605 : Nat.totient 101674952032842725405977097605 = 63330540571887612661485653760 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (1237, 1), (6737803, 1), (31685840967107443, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_5, prime_eightySixCF_7, prime_eightySixCF_11, prime_eightySixCF_1237, prime_eightySixCF_6737803, prime_eightySixCF_31685840967107443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097606 : Nat.totient 101674952032842725405977097606 = 50796762629324663200932903168 := by
  rw [← show ((([(2, 1), (1249, 1), (4684213, 1), (8689302311277267319, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_1249, prime_eightySixCF_4684213, prime_eightySixCF_8689302311277267319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097607 : Nat.totient 101674952032842725405977097607 = 64205749231203363215141409120 := by
  rw [← show ((([(3, 1), (19, 1), (9931, 1), (18119, 1), (9913155384968726459, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_19, prime_eightySixCF_9931, prime_eightySixCF_18119, prime_eightySixCF_9913155384968726459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097608 : Nat.totient 101674952032842725405977097608 = 49197557261928089491306626240 := by
  rw [← show ((([(2, 3), (31, 1), (283856533, 1), (1444319920914839987, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_31, prime_eightySixCF_283856533, prime_eightySixCF_1444319920914839987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097609 : Nat.totient 101674952032842725405977097609 = 101674952032842725405977097608 := by
  rw [← show ((([(101674952032842725405977097609, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_101674952032842725405977097609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097610 : Nat.totient 101674952032842725405977097610 = 27113320542091393441593892688 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (3389165067761424180199236587, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_5, prime_eightySixCF_3389165067761424180199236587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097611 : Nat.totient 101674952032842725405977097611 = 95672840180109752553143728128 := by
  rw [← show ((([(17, 1), (4507, 1), (1327020086830195191871169, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_17, prime_eightySixCF_4507, prime_eightySixCF_1327020086830195191871169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097612 : Nat.totient 101674952032842725405977097612 = 41212086846765859079848995840 := by
  rw [← show ((([(2, 2), (7, 1), (23, 1), (89, 1), (4578467, 1), (387452095336285321, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_7, prime_eightySixCF_23, prime_eightySixCF_89, prime_eightySixCF_4578467, prime_eightySixCF_387452095336285321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097613 : Nat.totient 101674952032842725405977097613 = 62549867984917542024139344000 := by
  rw [← show ((([(3, 2), (13, 1), (4679, 1), (10531, 1), (3012871, 1), (5853625302691, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_13, prime_eightySixCF_4679, prime_eightySixCF_10531, prime_eightySixCF_3012871, prime_eightySixCF_5853625302691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097614 : Nat.totient 101674952032842725405977097614 = 50836901666031968813246806656 := by
  rw [← show ((([(2, 1), (88513, 1), (574350389393889741653639, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_88513, prime_eightySixCF_574350389393889741653639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097615 : Nat.totient 101674952032842725405977097615 = 78650175658253498335432683520 := by
  rw [← show ((([(5, 1), (47, 1), (83, 1), (26777921921, 1), (194666468652863, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_5, prime_eightySixCF_47, prime_eightySixCF_83, prime_eightySixCF_26777921921, prime_eightySixCF_194666468652863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097616 : Nat.totient 101674952032842725405977097616 = 30810068402720131035761152000 := by
  rw [← show ((([(2, 4), (3, 1), (11, 1), (58913, 1), (223609319, 1), (14617699037951, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_11, prime_eightySixCF_58913, prime_eightySixCF_223609319, prime_eightySixCF_14617699037951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097617 : Nat.totient 101674952032842725405977097617 = 101579302971664133942754164196 := by
  rw [← show ((([(1063, 1), (95649061178591463222932359, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_1063, prime_eightySixCF_95649061178591463222932359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097618 : Nat.totient 101674952032842725405977097618 = 50531208335474624668436608000 := by
  rw [← show ((([(2, 1), (173, 1), (4073, 1), (8761719101, 1), (8234441369321, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_173, prime_eightySixCF_4073, prime_eightySixCF_8761719101, prime_eightySixCF_8234441369321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097619 : Nat.totient 101674952032842725405977097619 = 56061628066477216124093952000 := by
  rw [← show ((([(3, 1), (7, 1), (59, 1), (61, 1), (479, 1), (198272609, 1), (14164935458551, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_7, prime_eightySixCF_59, prime_eightySixCF_61, prime_eightySixCF_479, prime_eightySixCF_198272609, prime_eightySixCF_14164935458551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097620 : Nat.totient 101674952032842725405977097620 = 40162048605052450711879974912 := by
  rw [← show ((([(2, 2), (5, 1), (113, 1), (313, 1), (2089, 1), (4632373687, 1), (14853170743, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_5, prime_eightySixCF_113, prime_eightySixCF_313, prime_eightySixCF_2089, prime_eightySixCF_4632373687, prime_eightySixCF_14853170743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097621 : Nat.totient 101674952032842725405977097621 = 101616284912519168428785695280 := by
  rw [← show ((([(1741, 1), (380867, 1), (153335198581199446243, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_1741, prime_eightySixCF_380867, prime_eightySixCF_153335198581199446243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097622 : Nat.totient 101674952032842725405977097622 = 33890607952821490308203506752 := by
  rw [← show ((([(2, 1), (3, 3), (32503, 1), (33770048863, 1), (1715398711337, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_32503, prime_eightySixCF_33770048863, prime_eightySixCF_1715398711337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097623 : Nat.totient 101674952032842725405977097623 = 101106935541039134761250968408 := by
  rw [← show ((([(179, 1), (568016491803590644726129037, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_179, prime_eightySixCF_568016491803590644726129037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097624 : Nat.totient 101674952032842725405977097624 = 49083364297496560498540423168 := by
  rw [← show ((([(2, 3), (29, 1), (44819, 1), (366911537, 1), (26650322031269, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_29, prime_eightySixCF_44819, prime_eightySixCF_366911537, prime_eightySixCF_26650322031269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097625 : Nat.totient 101674952032842725405977097625 = 54226641084182786883187785200 := by
  rw [← show ((([(3, 1), (5, 3), (271133205420913934415938927, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_5, prime_eightySixCF_271133205420913934415938927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097626 : Nat.totient 101674952032842725405977097626 = 37176638924110700426341501440 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (19, 1), (41, 1), (717141954554604560693317, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_7, prime_eightySixCF_13, prime_eightySixCF_19, prime_eightySixCF_41, prime_eightySixCF_717141954554604560693317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097627 : Nat.totient 101674952032842725405977097627 = 92320443477404889584302080000 := by
  rw [← show ((([(11, 1), (1489, 1), (1879, 1), (1016401, 1), (21583087, 1), (150598681, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_11, prime_eightySixCF_1489, prime_eightySixCF_1879, prime_eightySixCF_1016401, prime_eightySixCF_21583087, prime_eightySixCF_150598681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097628 : Nat.totient 101674952032842725405977097628 = 31591939674526969115595571200 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (107, 1), (6421, 1), (10513, 1), (695047, 1), (99278801021, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_17, prime_eightySixCF_107, prime_eightySixCF_6421, prime_eightySixCF_10513, prime_eightySixCF_695047, prime_eightySixCF_99278801021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097629 : Nat.totient 101674952032842725405977097629 = 101288310698900137221384907968 := by
  rw [← show ((([(263, 1), (2623757, 1), (17012323, 1), (8661059012653, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_263, prime_eightySixCF_2623757, prime_eightySixCF_17012323, prime_eightySixCF_8661059012653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097630 : Nat.totient 101674952032842725405977097630 = 40643988918361885454437416960 := by
  rw [← show ((([(2, 1), (5, 1), (1627, 1), (44257, 1), (530641, 1), (266099249068937, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_5, prime_eightySixCF_1627, prime_eightySixCF_44257, prime_eightySixCF_530641, prime_eightySixCF_266099249068937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097631 : Nat.totient 101674952032842725405977097631 = 66206945509758053752729272624 := by
  rw [← show ((([(3, 2), (43, 1), (262725974245071641875909813, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_43, prime_eightySixCF_262725974245071641875909813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097632 : Nat.totient 101674952032842725405977097632 = 50837476016418718271679417792 := by
  rw [← show ((([(2, 5), (22208553183263, 1), (143068403637427, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_22208553183263, prime_eightySixCF_143068403637427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097633 : Nat.totient 101674952032842725405977097633 = 87149958885293764633694655108 := by
  rw [← show ((([(7, 1), (14524993147548960772282442519, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_7, prime_eightySixCF_14524993147548960772282442519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097634 : Nat.totient 101674952032842725405977097634 = 32975153647303508163649204416 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (65183, 1), (57061003, 1), (123136627768003, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_37, prime_eightySixCF_65183, prime_eightySixCF_57061003, prime_eightySixCF_123136627768003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097635 : Nat.totient 101674952032842725405977097635 = 76335452092254029771575253632 := by
  rw [← show ((([(5, 1), (23, 1), (53, 1), (16681698446733835177354733, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_5, prime_eightySixCF_23, prime_eightySixCF_53, prime_eightySixCF_16681698446733835177354733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097636 : Nat.totient 101674952032842725405977097636 = 50647636577121088847281568640 := by
  rw [← show ((([(2, 2), (269, 1), (59467, 1), (60865621, 1), (26106798535723, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_269, prime_eightySixCF_59467, prime_eightySixCF_60865621, prime_eightySixCF_26106798535723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097637 : Nat.totient 101674952032842725405977097637 = 67632937537059929691206372592 := by
  rw [← show ((([(3, 1), (523, 1), (3259, 1), (19884133584839184445247, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_523, prime_eightySixCF_3259, prime_eightySixCF_19884133584839184445247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097638 : Nat.totient 101674952032842725405977097638 = 46215887287651152439777862640 := by
  rw [← show ((([(2, 1), (11, 2), (16245680277623, 1), (25861916688493, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_11, prime_eightySixCF_16245680277623, prime_eightySixCF_25861916688493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097639 : Nat.totient 101674952032842725405977097639 = 90650855263768916249026713600 := by
  rw [← show ((([(13, 1), (31, 1), (577, 1), (5039, 1), (86773828379402302771, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_13, prime_eightySixCF_31, prime_eightySixCF_577, prime_eightySixCF_5039, prime_eightySixCF_86773828379402302771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097640 : Nat.totient 101674952032842725405977097640 = 23239989036078337235651904000 := by
  rw [← show ((([(2, 3), (3, 2), (5, 1), (7, 2), (5763886169662286020747001, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_5, prime_eightySixCF_7, prime_eightySixCF_5763886169662286020747001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097641 : Nat.totient 101674952032842725405977097641 = 101674952032842725405977097640 := by
  rw [← show ((([(101674952032842725405977097641, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_101674952032842725405977097641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097642 : Nat.totient 101674952032842725405977097642 = 50750870433859166944893668928 := by
  rw [← show ((([(2, 1), (587, 1), (31438890289, 1), (2754727668559247, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_587, prime_eightySixCF_31438890289, prime_eightySixCF_2754727668559247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097643 : Nat.totient 101674952032842725405977097643 = 67783301350754514050051122464 := by
  rw [← show ((([(3, 1), (15150595237, 1), (2236984761816209413, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_15150595237, prime_eightySixCF_2236984761816209413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097644 : Nat.totient 101674952032842725405977097644 = 49873838602051899238003200000 := by
  rw [← show ((([(2, 2), (103, 1), (151, 1), (859, 1), (911, 1), (2113, 1), (988390983653951, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_103, prime_eightySixCF_151, prime_eightySixCF_859, prime_eightySixCF_911, prime_eightySixCF_2113, prime_eightySixCF_988390983653951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097645 : Nat.totient 101674952032842725405977097645 = 72526033895604320141216510976 := by
  rw [← show ((([(5, 1), (17, 1), (19, 1), (270294939917, 1), (232918258347919, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_5, prime_eightySixCF_17, prime_eightySixCF_19, prime_eightySixCF_270294939917, prime_eightySixCF_232918258347919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097646 : Nat.totient 101674952032842725405977097646 = 33891635988779735767792127544 := by
  rw [← show ((([(2, 1), (3, 1), (2307307, 1), (7344417253017097811863, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_2307307, prime_eightySixCF_7344417253017097811863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097647 : Nat.totient 101674952032842725405977097647 = 86698404694178252899841313792 := by
  rw [← show ((([(7, 1), (193, 1), (75259031852585288975556697, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_7, prime_eightySixCF_193, prime_eightySixCF_75259031852585288975556697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097648 : Nat.totient 101674952032842725405977097648 = 50837476016396243251334360064 := by
  rw [← show ((([(2, 4), (2025135185947, 1), (3137906321587649, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_2025135185947, prime_eightySixCF_3137906321587649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097649 : Nat.totient 101674952032842725405977097649 = 61621183050185046578686134480 := by
  rw [← show ((([(3, 3), (11, 1), (2780064750499, 1), (123140982875683, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_11, prime_eightySixCF_2780064750499, prime_eightySixCF_123140982875683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097650 : Nat.totient 101674952032842725405977097650 = 40499674588656417804044256000 := by
  rw [← show ((([(2, 1), (5, 2), (241, 1), (26111, 1), (323149452545771238703, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_5, prime_eightySixCF_241, prime_eightySixCF_26111, prime_eightySixCF_323149452545771238703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097651 : Nat.totient 101674952032842725405977097651 = 99779389303836486157434496800 := by
  rw [← show ((([(67, 1), (271, 1), (11821, 1), (473713395013476018683, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_67, prime_eightySixCF_271, prime_eightySixCF_11821, prime_eightySixCF_473713395013476018683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097652 : Nat.totient 101674952032842725405977097652 = 31237124817360328646916648960 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (659, 1), (10519153, 1), (94020637446457721, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_13, prime_eightySixCF_659, prime_eightySixCF_10519153, prime_eightySixCF_94020637446457721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097653 : Nat.totient 101674952032842725405977097653 = 97581081260367468608111377600 := by
  rw [← show ((([(29, 1), (167, 1), (936380891, 1), (22420586277429581, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_29, prime_eightySixCF_167, prime_eightySixCF_936380891, prime_eightySixCF_22420586277429581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097654 : Nat.totient 101674952032842725405977097654 = 43129588114362185604286041312 := by
  rw [← show ((([(2, 1), (7, 1), (149, 1), (283, 1), (172231758810787591864283, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_7, prime_eightySixCF_149, prime_eightySixCF_283, prime_eightySixCF_172231758810787591864283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097655 : Nat.totient 101674952032842725405977097655 = 54129285559378722709908464256 := by
  rw [← show ((([(3, 1), (5, 1), (557, 1), (78061987, 1), (155893468657663103, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_5, prime_eightySixCF_557, prime_eightySixCF_78061987, prime_eightySixCF_155893468657663103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097656 : Nat.totient 101674952032842725405977097656 = 50836834364046393671917500384 := by
  rw [← show ((([(2, 3), (79229, 1), (160413093742257767682883, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_79229, prime_eightySixCF_160413093742257767682883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097657 : Nat.totient 101674952032842725405977097657 = 101674943352145264623848867556 := by
  rw [← show ((([(11712763, 1), (8680697460782116517339, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_11712763, prime_eightySixCF_8680697460782116517339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097658 : Nat.totient 101674952032842725405977097658 = 32355015295839379634208706560 := by
  rw [← show ((([(2, 1), (3, 2), (23, 1), (641, 1), (3947, 1), (7507, 1), (12930700814475523, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_23, prime_eightySixCF_641, prime_eightySixCF_3947, prime_eightySixCF_7507, prime_eightySixCF_12930700814475523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097659 : Nat.totient 101674952032842725405977097659 = 100888799017808579224045457664 := by
  rw [← show ((([(137, 1), (2309, 1), (351157, 1), (915309871096497739, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_137, prime_eightySixCF_2309, prime_eightySixCF_351157, prime_eightySixCF_915309871096497739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097660 : Nat.totient 101674952032842725405977097660 = 36791618428551506194243564800 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (211, 1), (7187, 1), (49367, 1), (6173400588129287, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_5, prime_eightySixCF_11, prime_eightySixCF_211, prime_eightySixCF_7187, prime_eightySixCF_49367, prime_eightySixCF_6173400588129287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097661 : Nat.totient 101674952032842725405977097661 = 58099971875884129158648960000 := by
  rw [← show ((([(3, 1), (7, 1), (81337001, 1), (59525976160792063841, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_7, prime_eightySixCF_81337001, prime_eightySixCF_59525976160792063841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097662 : Nat.totient 101674952032842725405977097662 = 46187520526255143532163521536 := by
  rw [← show ((([(2, 1), (17, 1), (47, 1), (73, 1), (139387147, 1), (6253045835585099, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_17, prime_eightySixCF_47, prime_eightySixCF_73, prime_eightySixCF_139387147, prime_eightySixCF_6253045835585099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097663 : Nat.totient 101674952032842725405977097663 = 101467285674042303130440108000 := by
  rw [← show ((([(499, 1), (28547, 1), (286301, 1), (24930448444664771, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_499, prime_eightySixCF_28547, prime_eightySixCF_286301, prime_eightySixCF_24930448444664771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097664 : Nat.totient 101674952032842725405977097664 = 32107879589139939762017012736 := by
  rw [← show ((([(2, 6), (3, 1), (19, 1), (179766767837, 1), (155042133704539, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_19, prime_eightySixCF_179766767837, prime_eightySixCF_155042133704539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097665 : Nat.totient 101674952032842725405977097665 = 74394195805313636038657496064 := by
  rw [← show ((([(5, 1), (13, 1), (109, 1), (7374883, 1), (208234667, 1), (9344712709, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_5, prime_eightySixCF_13, prime_eightySixCF_109, prime_eightySixCF_7374883, prime_eightySixCF_208234667, prime_eightySixCF_9344712709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097666 : Nat.totient 101674952032842725405977097666 = 50833471814739404830294640208 := by
  rw [← show ((([(2, 1), (13789, 1), (160163, 1), (23019135744881434919, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_13789, prime_eightySixCF_160163, prime_eightySixCF_23019135744881434919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097667 : Nat.totient 101674952032842725405977097667 = 66130050102661935223399738080 := by
  rw [← show ((([(3, 2), (41, 1), (275541875427758063430832243, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_41, prime_eightySixCF_275541875427758063430832243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097668 : Nat.totient 101674952032842725405977097668 = 43568148437874559557430908768 := by
  rw [← show ((([(2, 2), (7, 1), (6379, 1), (569250397693563284695189, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_7, prime_eightySixCF_6379, prime_eightySixCF_569250397693563284695189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097669 : Nat.totient 101674952032842725405977097669 = 101642988828600974590273090800 := by
  rw [← show ((([(3181, 1), (493496450119, 1), (64768863132671, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3181, prime_eightySixCF_493496450119, prime_eightySixCF_64768863132671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097670 : Nat.totient 101674952032842725405977097670 = 26235744642580747707300556800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (31, 1), (8887, 1), (149603297, 1), (82230831681221, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_5, prime_eightySixCF_31, prime_eightySixCF_8887, prime_eightySixCF_149603297, prime_eightySixCF_82230831681221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097671 : Nat.totient 101674952032842725405977097671 = 89930081015305937106552727200 := by
  rw [← show ((([(11, 1), (37, 1), (25423, 1), (9826362229489105794911, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_11, prime_eightySixCF_37, prime_eightySixCF_25423, prime_eightySixCF_9826362229489105794911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097672 : Nat.totient 101674952032842725405977097672 = 50836168829329164466560916800 := by
  rw [← show ((([(2, 3), (38891, 1), (5864051159, 1), (55728471099661, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_38891, prime_eightySixCF_5864051159, prime_eightySixCF_55728471099661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097673 : Nat.totient 101674952032842725405977097673 = 66590575238024854033789094400 := by
  rw [← show ((([(3, 1), (71, 1), (281, 1), (325219, 1), (24207923, 1), (215771764693, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_71, prime_eightySixCF_281, prime_eightySixCF_325219, prime_eightySixCF_24207923, prime_eightySixCF_215771764693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097674 : Nat.totient 101674952032842725405977097674 = 49143186686160852011722211328 := by
  rw [← show ((([(2, 1), (43, 1), (97, 1), (434689, 1), (3720465179, 1), (7536468637, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_43, prime_eightySixCF_97, prime_eightySixCF_434689, prime_eightySixCF_3720465179, prime_eightySixCF_7536468637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097675 : Nat.totient 101674952032842725405977097675 = 68702195335232781006784220160 := by
  rw [← show ((([(5, 2), (7, 1), (79, 1), (509, 1), (43631343577, 1), (331155877183, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_5, prime_eightySixCF_7, prime_eightySixCF_79, prime_eightySixCF_509, prime_eightySixCF_43631343577, prime_eightySixCF_331155877183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097676 : Nat.totient 101674952032842725405977097676 = 33844513472221176097121645280 := by
  rw [← show ((([(2, 2), (3, 4), (719, 1), (436455605491349119172621, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_719, prime_eightySixCF_436455605491349119172621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097677 : Nat.totient 101674952032842725405977097677 = 101397908549571874612976943024 := by
  rw [← show ((([(367, 1), (5881104239, 1), (47107389151914029, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_367, prime_eightySixCF_5881104239, prime_eightySixCF_47107389151914029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097678 : Nat.totient 101674952032842725405977097678 = 46131529735892136168552841536 := by
  rw [← show ((([(2, 1), (13, 1), (59, 1), (66280933528580655414587417, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_13, prime_eightySixCF_59, prime_eightySixCF_66280933528580655414587417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097679 : Nat.totient 101674952032842725405977097679 = 63766835151553672766146713600 := by
  rw [← show ((([(3, 1), (17, 1), (2207, 1), (207821, 1), (591387427, 1), (7349874941, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_17, prime_eightySixCF_2207, prime_eightySixCF_207821, prime_eightySixCF_591387427, prime_eightySixCF_7349874941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097680 : Nat.totient 101674952032842725405977097680 = 39730494960892463460632524800 := by
  rw [← show ((([(2, 4), (5, 1), (61, 1), (197, 1), (571, 1), (185221680321024209803, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_5, prime_eightySixCF_61, prime_eightySixCF_197, prime_eightySixCF_571, prime_eightySixCF_185221680321024209803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097681 : Nat.totient 101674952032842725405977097681 = 97238850825470871727673496000 := by
  rw [← show ((([(23, 1), (6491, 1), (207877, 1), (247822231, 1), (13219889591, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_23, prime_eightySixCF_6491, prime_eightySixCF_207877, prime_eightySixCF_247822231, prime_eightySixCF_13219889591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097682 : Nat.totient 101674952032842725405977097682 = 25245960962653916491982976000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (101, 1), (152062966837, 1), (494116287107, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_7, prime_eightySixCF_11, prime_eightySixCF_29, prime_eightySixCF_101, prime_eightySixCF_152062966837, prime_eightySixCF_494116287107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097683 : Nat.totient 101674952032842725405977097683 = 96315317320494507106644202752 := by
  rw [← show ((([(19, 1), (11593, 1), (11486989, 1), (22757179, 1), (1765793479, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_19, prime_eightySixCF_11593, prime_eightySixCF_11486989, prime_eightySixCF_22757179, prime_eightySixCF_1765793479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097684 : Nat.totient 101674952032842725405977097684 = 50805980075794504321519274880 := by
  rw [← show ((([(2, 2), (1619, 1), (532561, 1), (29480699004321004519, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_1619, prime_eightySixCF_532561, prime_eightySixCF_29480699004321004519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097685 : Nat.totient 101674952032842725405977097685 = 54065498801219850411406646784 := by
  rw [← show ((([(3, 2), (5, 1), (349, 1), (9437, 1), (1528187, 1), (448916511623603, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_5, prime_eightySixCF_349, prime_eightySixCF_9437, prime_eightySixCF_1528187, prime_eightySixCF_448916511623603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097686 : Nat.totient 101674952032842725405977097686 = 50653457690267572973258698944 := by
  rw [← show ((([(2, 1), (317, 1), (2143, 1), (74834618199995823395353, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_317, prime_eightySixCF_2143, prime_eightySixCF_74834618199995823395353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097687 : Nat.totient 101674952032842725405977097687 = 101611760638531010063220783360 := by
  rw [← show ((([(1609, 1), (115591328911, 1), (546679357593713, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_1609, prime_eightySixCF_115591328911, prime_eightySixCF_546679357593713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097688 : Nat.totient 101674952032842725405977097688 = 33175381229004351249760813056 := by
  rw [← show ((([(2, 3), (3, 1), (53, 1), (433, 1), (3508529, 1), (52615523762625797, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_53, prime_eightySixCF_433, prime_eightySixCF_3508529, prime_eightySixCF_52615523762625797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097689 : Nat.totient 101674952032842725405977097689 = 87149507310044735954812230600 := by
  rw [← show ((([(7, 2), (192991, 1), (10751791643539973198071, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_7, prime_eightySixCF_192991, prime_eightySixCF_10751791643539973198071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097690 : Nat.totient 101674952032842725405977097690 = 40669979542869075640230191104 := by
  rw [← show ((([(2, 1), (5, 1), (34554089, 1), (436312433, 1), (674399034737, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_5, prime_eightySixCF_34554089, prime_eightySixCF_436312433, prime_eightySixCF_674399034737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097691 : Nat.totient 101674952032842725405977097691 = 62569197651813712673609112480 := by
  rw [← show ((([(3, 1), (13, 1), (17384359, 1), (149965267751556007691, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_13, prime_eightySixCF_17384359, prime_eightySixCF_149965267751556007691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097692 : Nat.totient 101674952032842725405977097692 = 50781424805020485148843783920 := by
  rw [← show ((([(2, 2), (907, 1), (47350271, 1), (591867139869379259, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_907, prime_eightySixCF_47350271, prime_eightySixCF_591867139869379259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097693 : Nat.totient 101674952032842725405977097693 = 92431774486861940650953427200 := by
  rw [← show ((([(11, 1), (1045021633, 1), (8844962788948462711, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_11, prime_eightySixCF_1045021633, prime_eightySixCF_8844962788948462711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097694 : Nat.totient 101674952032842725405977097694 = 33891650677614241801992365892 := by
  rw [← show ((([(2, 1), (3, 2), (5648608446269040300332060983, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_5648608446269040300332060983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097695 : Nat.totient 101674952032842725405977097695 = 80840983315126797261893998080 := by
  rw [← show ((([(5, 1), (191, 1), (1213, 1), (21383, 1), (30763, 1), (133429691622677, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_5, prime_eightySixCF_191, prime_eightySixCF_1213, prime_eightySixCF_21383, prime_eightySixCF_30763, prime_eightySixCF_133429691622677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097696 : Nat.totient 101674952032842725405977097696 = 41011745357785301004091600896 := by
  rw [← show ((([(2, 5), (7, 1), (17, 1), (26700355050641472007872137, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_7, prime_eightySixCF_17, prime_eightySixCF_26700355050641472007872137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097697 : Nat.totient 101674952032842725405977097697 = 67254977221915414062311980800 := by
  rw [← show ((([(3, 1), (131, 1), (11981, 1), (12739, 1), (1184803733, 1), (1430693507, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_3, prime_eightySixCF_131, prime_eightySixCF_11981, prime_eightySixCF_12739, prime_eightySixCF_1184803733, prime_eightySixCF_1430693507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097698 : Nat.totient 101674952032842725405977097698 = 50221409698940936252122291200 := by
  rw [← show ((([(2, 1), (83, 1), (14461, 1), (537281, 1), (78832641543957383, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_83, prime_eightySixCF_14461, prime_eightySixCF_537281, prime_eightySixCF_78832641543957383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097699 : Nat.totient 101674952032842725405977097699 = 101674952032842725405977097698 := by
  rw [← show ((([(101674952032842725405977097699, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_101674952032842725405977097699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097700 : Nat.totient 101674952032842725405977097700 = 27109257293686878499223698560 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (6719, 1), (970699, 1), (51964110565327039, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_2, prime_eightySixCF_3, prime_eightySixCF_5, prime_eightySixCF_6719, prime_eightySixCF_970699, prime_eightySixCF_51964110565327039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightySixCF_101674952032842725405977097701 : Nat.totient 101674952032842725405977097701 = 96523492307006563160627865600 := by
  rw [← show ((([(31, 1), (89, 1), (127, 1), (7911508541, 1), (36677460114577, 1)] : List FactorBlock).map factorBlockValue).prod) = 101674952032842725405977097701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightySixCF_31, prime_eightySixCF_89, prime_eightySixCF_127, prime_eightySixCF_7911508541, prime_eightySixCF_36677460114577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightySixCF : certifiedKill 1 101674952032842725405977097599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightySixCF_101674952032842725405977097600, phi_eightySixCF_101674952032842725405977097601, phi_eightySixCF_101674952032842725405977097602,
    phi_eightySixCF_101674952032842725405977097603, phi_eightySixCF_101674952032842725405977097604, phi_eightySixCF_101674952032842725405977097605,
    phi_eightySixCF_101674952032842725405977097606, phi_eightySixCF_101674952032842725405977097607, phi_eightySixCF_101674952032842725405977097608,
    phi_eightySixCF_101674952032842725405977097609, phi_eightySixCF_101674952032842725405977097610, phi_eightySixCF_101674952032842725405977097611,
    phi_eightySixCF_101674952032842725405977097612, phi_eightySixCF_101674952032842725405977097613, phi_eightySixCF_101674952032842725405977097614,
    phi_eightySixCF_101674952032842725405977097615, phi_eightySixCF_101674952032842725405977097616, phi_eightySixCF_101674952032842725405977097617,
    phi_eightySixCF_101674952032842725405977097618, phi_eightySixCF_101674952032842725405977097619, phi_eightySixCF_101674952032842725405977097620,
    phi_eightySixCF_101674952032842725405977097621, phi_eightySixCF_101674952032842725405977097622, phi_eightySixCF_101674952032842725405977097623,
    phi_eightySixCF_101674952032842725405977097624, phi_eightySixCF_101674952032842725405977097625, phi_eightySixCF_101674952032842725405977097626,
    phi_eightySixCF_101674952032842725405977097627, phi_eightySixCF_101674952032842725405977097628, phi_eightySixCF_101674952032842725405977097629,
    phi_eightySixCF_101674952032842725405977097630, phi_eightySixCF_101674952032842725405977097631, phi_eightySixCF_101674952032842725405977097632,
    phi_eightySixCF_101674952032842725405977097633, phi_eightySixCF_101674952032842725405977097634, phi_eightySixCF_101674952032842725405977097635,
    phi_eightySixCF_101674952032842725405977097636, phi_eightySixCF_101674952032842725405977097637, phi_eightySixCF_101674952032842725405977097638,
    phi_eightySixCF_101674952032842725405977097639, phi_eightySixCF_101674952032842725405977097640, phi_eightySixCF_101674952032842725405977097641,
    phi_eightySixCF_101674952032842725405977097642, phi_eightySixCF_101674952032842725405977097643, phi_eightySixCF_101674952032842725405977097644,
    phi_eightySixCF_101674952032842725405977097645, phi_eightySixCF_101674952032842725405977097646, phi_eightySixCF_101674952032842725405977097647,
    phi_eightySixCF_101674952032842725405977097648, phi_eightySixCF_101674952032842725405977097649, phi_eightySixCF_101674952032842725405977097650,
    phi_eightySixCF_101674952032842725405977097651, phi_eightySixCF_101674952032842725405977097652, phi_eightySixCF_101674952032842725405977097653,
    phi_eightySixCF_101674952032842725405977097654, phi_eightySixCF_101674952032842725405977097655, phi_eightySixCF_101674952032842725405977097656,
    phi_eightySixCF_101674952032842725405977097657, phi_eightySixCF_101674952032842725405977097658, phi_eightySixCF_101674952032842725405977097659,
    phi_eightySixCF_101674952032842725405977097660, phi_eightySixCF_101674952032842725405977097661, phi_eightySixCF_101674952032842725405977097662,
    phi_eightySixCF_101674952032842725405977097663, phi_eightySixCF_101674952032842725405977097664, phi_eightySixCF_101674952032842725405977097665,
    phi_eightySixCF_101674952032842725405977097666, phi_eightySixCF_101674952032842725405977097667, phi_eightySixCF_101674952032842725405977097668,
    phi_eightySixCF_101674952032842725405977097669, phi_eightySixCF_101674952032842725405977097670, phi_eightySixCF_101674952032842725405977097671,
    phi_eightySixCF_101674952032842725405977097672, phi_eightySixCF_101674952032842725405977097673, phi_eightySixCF_101674952032842725405977097674,
    phi_eightySixCF_101674952032842725405977097675, phi_eightySixCF_101674952032842725405977097676, phi_eightySixCF_101674952032842725405977097677,
    phi_eightySixCF_101674952032842725405977097678, phi_eightySixCF_101674952032842725405977097679, phi_eightySixCF_101674952032842725405977097680,
    phi_eightySixCF_101674952032842725405977097681, phi_eightySixCF_101674952032842725405977097682, phi_eightySixCF_101674952032842725405977097683,
    phi_eightySixCF_101674952032842725405977097684, phi_eightySixCF_101674952032842725405977097685, phi_eightySixCF_101674952032842725405977097686,
    phi_eightySixCF_101674952032842725405977097687, phi_eightySixCF_101674952032842725405977097688, phi_eightySixCF_101674952032842725405977097689,
    phi_eightySixCF_101674952032842725405977097690, phi_eightySixCF_101674952032842725405977097691, phi_eightySixCF_101674952032842725405977097692,
    phi_eightySixCF_101674952032842725405977097693, phi_eightySixCF_101674952032842725405977097694, phi_eightySixCF_101674952032842725405977097695,
    phi_eightySixCF_101674952032842725405977097696, phi_eightySixCF_101674952032842725405977097697, phi_eightySixCF_101674952032842725405977097698,
    phi_eightySixCF_101674952032842725405977097699, phi_eightySixCF_101674952032842725405977097700, phi_eightySixCF_101674952032842725405977097701]

end TotientTailPeriodKiller
end Erdos249257
