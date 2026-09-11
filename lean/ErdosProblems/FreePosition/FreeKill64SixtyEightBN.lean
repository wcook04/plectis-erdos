import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyEightBNFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyEightBNFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : sixtyEightBNFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyEightBNFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyEightBNFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyEightBNFastPow a n * sixtyEightBNFastPow a n * a else sixtyEightBNFastPow a n * sixtyEightBNFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyEightBN_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtyEightBN_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtyEightBN_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtyEightBN_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtyEightBN_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtyEightBN_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtyEightBN_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtyEightBN_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtyEightBN_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtyEightBN_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtyEightBN_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtyEightBN_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtyEightBN_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtyEightBN_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtyEightBN_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtyEightBN_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtyEightBN_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtyEightBN_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtyEightBN_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtyEightBN_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtyEightBN_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtyEightBN_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtyEightBN_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtyEightBN_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtyEightBN_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtyEightBN_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtyEightBN_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtyEightBN_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtyEightBN_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtyEightBN_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtyEightBN_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtyEightBN_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtyEightBN_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtyEightBN_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixtyEightBN_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtyEightBN_151 : Nat.Prime 151 := by norm_num
private theorem prime_sixtyEightBN_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixtyEightBN_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtyEightBN_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixtyEightBN_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtyEightBN_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtyEightBN_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixtyEightBN_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixtyEightBN_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixtyEightBN_197 : Nat.Prime 197 := by norm_num
private theorem prime_sixtyEightBN_199 : Nat.Prime 199 := by norm_num
private theorem prime_sixtyEightBN_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtyEightBN_223 : Nat.Prime 223 := by norm_num
private theorem prime_sixtyEightBN_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixtyEightBN_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixtyEightBN_241 : Nat.Prime 241 := by norm_num
private theorem prime_sixtyEightBN_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtyEightBN_257 : Nat.Prime 257 := by norm_num
private theorem prime_sixtyEightBN_263 : Nat.Prime 263 := by norm_num
private theorem prime_sixtyEightBN_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixtyEightBN_271 : Nat.Prime 271 := by norm_num
private theorem prime_sixtyEightBN_277 : Nat.Prime 277 := by norm_num
private theorem prime_sixtyEightBN_281 : Nat.Prime 281 := by norm_num
private theorem prime_sixtyEightBN_293 : Nat.Prime 293 := by norm_num
private theorem prime_sixtyEightBN_307 : Nat.Prime 307 := by norm_num
private theorem prime_sixtyEightBN_311 : Nat.Prime 311 := by norm_num
private theorem prime_sixtyEightBN_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtyEightBN_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtyEightBN_337 : Nat.Prime 337 := by norm_num
private theorem prime_sixtyEightBN_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtyEightBN_359 : Nat.Prime 359 := by norm_num
private theorem prime_sixtyEightBN_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtyEightBN_397 : Nat.Prime 397 := by norm_num
private theorem prime_sixtyEightBN_401 : Nat.Prime 401 := by norm_num
private theorem prime_sixtyEightBN_433 : Nat.Prime 433 := by norm_num
private theorem prime_sixtyEightBN_443 : Nat.Prime 443 := by norm_num
private theorem prime_sixtyEightBN_449 : Nat.Prime 449 := by norm_num
private theorem prime_sixtyEightBN_457 : Nat.Prime 457 := by norm_num
private theorem prime_sixtyEightBN_461 : Nat.Prime 461 := by norm_num
private theorem prime_sixtyEightBN_463 : Nat.Prime 463 := by norm_num
private theorem prime_sixtyEightBN_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixtyEightBN_487 : Nat.Prime 487 := by norm_num
private theorem prime_sixtyEightBN_491 : Nat.Prime 491 := by norm_num
private theorem prime_sixtyEightBN_499 : Nat.Prime 499 := by norm_num
private theorem prime_sixtyEightBN_521 : Nat.Prime 521 := by norm_num
private theorem prime_sixtyEightBN_541 : Nat.Prime 541 := by norm_num
private theorem prime_sixtyEightBN_547 : Nat.Prime 547 := by norm_num
private theorem prime_sixtyEightBN_563 : Nat.Prime 563 := by norm_num
private theorem prime_sixtyEightBN_599 : Nat.Prime 599 := by norm_num
private theorem prime_sixtyEightBN_613 : Nat.Prime 613 := by norm_num
private theorem prime_sixtyEightBN_617 : Nat.Prime 617 := by norm_num
private theorem prime_sixtyEightBN_647 : Nat.Prime 647 := by norm_num
private theorem prime_sixtyEightBN_659 : Nat.Prime 659 := by norm_num
private theorem prime_sixtyEightBN_661 : Nat.Prime 661 := by norm_num
private theorem prime_sixtyEightBN_677 : Nat.Prime 677 := by norm_num
private theorem prime_sixtyEightBN_683 : Nat.Prime 683 := by norm_num
private theorem prime_sixtyEightBN_691 : Nat.Prime 691 := by norm_num
private theorem prime_sixtyEightBN_701 : Nat.Prime 701 := by norm_num
private theorem prime_sixtyEightBN_709 : Nat.Prime 709 := by norm_num
private theorem prime_sixtyEightBN_719 : Nat.Prime 719 := by norm_num
private theorem prime_sixtyEightBN_743 : Nat.Prime 743 := by norm_num
private theorem prime_sixtyEightBN_773 : Nat.Prime 773 := by norm_num
private theorem prime_sixtyEightBN_787 : Nat.Prime 787 := by norm_num
private theorem prime_sixtyEightBN_809 : Nat.Prime 809 := by norm_num
private theorem prime_sixtyEightBN_821 : Nat.Prime 821 := by norm_num
private theorem prime_sixtyEightBN_823 : Nat.Prime 823 := by norm_num
private theorem prime_sixtyEightBN_829 : Nat.Prime 829 := by norm_num
private theorem prime_sixtyEightBN_853 : Nat.Prime 853 := by norm_num
private theorem prime_sixtyEightBN_857 : Nat.Prime 857 := by norm_num
private theorem prime_sixtyEightBN_863 : Nat.Prime 863 := by norm_num
private theorem prime_sixtyEightBN_881 : Nat.Prime 881 := by norm_num
private theorem prime_sixtyEightBN_911 : Nat.Prime 911 := by norm_num
private theorem prime_sixtyEightBN_947 : Nat.Prime 947 := by norm_num
private theorem prime_sixtyEightBN_967 : Nat.Prime 967 := by norm_num
private theorem prime_sixtyEightBN_971 : Nat.Prime 971 := by norm_num
private theorem prime_sixtyEightBN_983 : Nat.Prime 983 := by norm_num
private theorem prime_sixtyEightBN_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_sixtyEightBN_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_sixtyEightBN_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_sixtyEightBN_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_sixtyEightBN_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_sixtyEightBN_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_sixtyEightBN_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_sixtyEightBN_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_sixtyEightBN_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_sixtyEightBN_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_sixtyEightBN_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_sixtyEightBN_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_sixtyEightBN_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_sixtyEightBN_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_sixtyEightBN_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_sixtyEightBN_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_sixtyEightBN_1571 : Nat.Prime 1571 := by norm_num
private theorem prime_sixtyEightBN_1583 : Nat.Prime 1583 := by norm_num
private theorem prime_sixtyEightBN_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_sixtyEightBN_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_sixtyEightBN_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_sixtyEightBN_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_sixtyEightBN_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_sixtyEightBN_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_sixtyEightBN_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_sixtyEightBN_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_sixtyEightBN_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_sixtyEightBN_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_sixtyEightBN_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_sixtyEightBN_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_sixtyEightBN_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_sixtyEightBN_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_sixtyEightBN_2393 : Nat.Prime 2393 := by norm_num
private theorem prime_sixtyEightBN_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_sixtyEightBN_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_sixtyEightBN_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_sixtyEightBN_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_sixtyEightBN_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_sixtyEightBN_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_sixtyEightBN_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_sixtyEightBN_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_sixtyEightBN_3037 : Nat.Prime 3037 := by norm_num
private theorem prime_sixtyEightBN_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_sixtyEightBN_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_sixtyEightBN_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_sixtyEightBN_3257 : Nat.Prime 3257 := by norm_num
private theorem prime_sixtyEightBN_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_sixtyEightBN_3361 : Nat.Prime 3361 := by norm_num
private theorem prime_sixtyEightBN_3541 : Nat.Prime 3541 := by norm_num
private theorem prime_sixtyEightBN_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_sixtyEightBN_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_sixtyEightBN_3907 : Nat.Prime 3907 := by norm_num
private theorem prime_sixtyEightBN_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_sixtyEightBN_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_sixtyEightBN_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_sixtyEightBN_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_sixtyEightBN_4441 : Nat.Prime 4441 := by norm_num
private theorem prime_sixtyEightBN_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_sixtyEightBN_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_sixtyEightBN_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_sixtyEightBN_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_sixtyEightBN_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_sixtyEightBN_5737 : Nat.Prime 5737 := by norm_num
private theorem prime_sixtyEightBN_5741 : Nat.Prime 5741 := by norm_num
private theorem prime_sixtyEightBN_5953 : Nat.Prime 5953 := by norm_num
private theorem prime_sixtyEightBN_6053 : Nat.Prime 6053 := by norm_num
private theorem prime_sixtyEightBN_6277 : Nat.Prime 6277 := by norm_num
private theorem prime_sixtyEightBN_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_sixtyEightBN_6421 : Nat.Prime 6421 := by norm_num
private theorem prime_sixtyEightBN_6469 : Nat.Prime 6469 := by norm_num
private theorem prime_sixtyEightBN_6563 : Nat.Prime 6563 := by norm_num
private theorem prime_sixtyEightBN_6653 : Nat.Prime 6653 := by norm_num
private theorem prime_sixtyEightBN_6691 : Nat.Prime 6691 := by norm_num
private theorem prime_sixtyEightBN_6781 : Nat.Prime 6781 := by norm_num
private theorem prime_sixtyEightBN_6967 : Nat.Prime 6967 := by norm_num
private theorem prime_sixtyEightBN_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_sixtyEightBN_7351 : Nat.Prime 7351 := by norm_num
private theorem prime_sixtyEightBN_7523 : Nat.Prime 7523 := by norm_num
private theorem prime_sixtyEightBN_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_sixtyEightBN_8093 : Nat.Prime 8093 := by norm_num
private theorem prime_sixtyEightBN_8803 : Nat.Prime 8803 := by norm_num
private theorem prime_sixtyEightBN_9173 : Nat.Prime 9173 := by norm_num
private theorem prime_sixtyEightBN_9283 : Nat.Prime 9283 := by norm_num
private theorem prime_sixtyEightBN_9767 : Nat.Prime 9767 := by norm_num
private theorem prime_sixtyEightBN_9973 : Nat.Prime 9973 := by norm_num
private theorem prime_sixtyEightBN_10433 : Nat.Prime 10433 := by norm_num
private theorem prime_sixtyEightBN_10597 : Nat.Prime 10597 := by norm_num
private theorem prime_sixtyEightBN_10667 : Nat.Prime 10667 := by norm_num
private theorem prime_sixtyEightBN_10949 : Nat.Prime 10949 := by norm_num
private theorem prime_sixtyEightBN_11027 : Nat.Prime 11027 := by norm_num
private theorem prime_sixtyEightBN_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_sixtyEightBN_12239 : Nat.Prime 12239 := by norm_num
private theorem prime_sixtyEightBN_12263 : Nat.Prime 12263 := by norm_num
private theorem prime_sixtyEightBN_12377 : Nat.Prime 12377 := by norm_num
private theorem prime_sixtyEightBN_12433 : Nat.Prime 12433 := by norm_num
private theorem prime_sixtyEightBN_12601 : Nat.Prime 12601 := by norm_num
private theorem prime_sixtyEightBN_12611 : Nat.Prime 12611 := by norm_num
private theorem prime_sixtyEightBN_13759 : Nat.Prime 13759 := by norm_num
private theorem prime_sixtyEightBN_13781 : Nat.Prime 13781 := by norm_num
private theorem prime_sixtyEightBN_14591 : Nat.Prime 14591 := by norm_num
private theorem prime_sixtyEightBN_14779 : Nat.Prime 14779 := by norm_num
private theorem prime_sixtyEightBN_14891 : Nat.Prime 14891 := by norm_num
private theorem prime_sixtyEightBN_15259 : Nat.Prime 15259 := by norm_num
private theorem prime_sixtyEightBN_15671 : Nat.Prime 15671 := by norm_num
private theorem prime_sixtyEightBN_15739 : Nat.Prime 15739 := by norm_num
private theorem prime_sixtyEightBN_15791 : Nat.Prime 15791 := by norm_num
private theorem prime_sixtyEightBN_16561 : Nat.Prime 16561 := by norm_num
private theorem prime_sixtyEightBN_17609 : Nat.Prime 17609 := by norm_num
private theorem prime_sixtyEightBN_17881 : Nat.Prime 17881 := by norm_num
private theorem prime_sixtyEightBN_18553 : Nat.Prime 18553 := by norm_num
private theorem prime_sixtyEightBN_18919 : Nat.Prime 18919 := by norm_num
private theorem prime_sixtyEightBN_19301 : Nat.Prime 19301 := by norm_num
private theorem prime_sixtyEightBN_19819 : Nat.Prime 19819 := by norm_num
private theorem prime_sixtyEightBN_20533 : Nat.Prime 20533 := by norm_num
private theorem prime_sixtyEightBN_22369 : Nat.Prime 22369 := by norm_num
private theorem prime_sixtyEightBN_22963 : Nat.Prime 22963 := by norm_num
private theorem prime_sixtyEightBN_23357 : Nat.Prime 23357 := by norm_num
private theorem prime_sixtyEightBN_24019 : Nat.Prime 24019 := by norm_num
private theorem prime_sixtyEightBN_25219 : Nat.Prime 25219 := by norm_num
private theorem prime_sixtyEightBN_26017 : Nat.Prime 26017 := by norm_num
private theorem prime_sixtyEightBN_28027 : Nat.Prime 28027 := by norm_num
private theorem prime_sixtyEightBN_29803 : Nat.Prime 29803 := by norm_num
private theorem prime_sixtyEightBN_30781 : Nat.Prime 30781 := by norm_num
private theorem prime_sixtyEightBN_32573 : Nat.Prime 32573 := by norm_num
private theorem prime_sixtyEightBN_33749 : Nat.Prime 33749 := by norm_num
private theorem prime_sixtyEightBN_34613 : Nat.Prime 34613 := by norm_num
private theorem prime_sixtyEightBN_35251 : Nat.Prime 35251 := by norm_num
private theorem prime_sixtyEightBN_35899 : Nat.Prime 35899 := by norm_num
private theorem prime_sixtyEightBN_35977 : Nat.Prime 35977 := by norm_num
private theorem prime_sixtyEightBN_36161 : Nat.Prime 36161 := by norm_num
private theorem prime_sixtyEightBN_37783 : Nat.Prime 37783 := by norm_num
private theorem prime_sixtyEightBN_38593 : Nat.Prime 38593 := by norm_num
private theorem prime_sixtyEightBN_40507 : Nat.Prime 40507 := by norm_num
private theorem prime_sixtyEightBN_40627 : Nat.Prime 40627 := by norm_num
private theorem prime_sixtyEightBN_43541 : Nat.Prime 43541 := by norm_num
private theorem prime_sixtyEightBN_46819 : Nat.Prime 46819 := by norm_num
private theorem prime_sixtyEightBN_46853 : Nat.Prime 46853 := by norm_num
private theorem prime_sixtyEightBN_48757 : Nat.Prime 48757 := by norm_num
private theorem prime_sixtyEightBN_49081 : Nat.Prime 49081 := by norm_num
private theorem prime_sixtyEightBN_49531 : Nat.Prime 49531 := by norm_num
private theorem prime_sixtyEightBN_50627 : Nat.Prime 50627 := by norm_num
private theorem prime_sixtyEightBN_55207 : Nat.Prime 55207 := by norm_num
private theorem prime_sixtyEightBN_55987 : Nat.Prime 55987 := by norm_num
private theorem prime_sixtyEightBN_56179 : Nat.Prime 56179 := by norm_num
private theorem prime_sixtyEightBN_56369 : Nat.Prime 56369 := by norm_num
private theorem prime_sixtyEightBN_56533 : Nat.Prime 56533 := by norm_num
private theorem prime_sixtyEightBN_56687 : Nat.Prime 56687 := by norm_num
private theorem prime_sixtyEightBN_57697 : Nat.Prime 57697 := by norm_num
private theorem prime_sixtyEightBN_59669 : Nat.Prime 59669 := by norm_num
private theorem prime_sixtyEightBN_63419 : Nat.Prime 63419 := by norm_num
private theorem prime_sixtyEightBN_70223 : Nat.Prime 70223 := by norm_num
private theorem prime_sixtyEightBN_73013 : Nat.Prime 73013 := by norm_num
private theorem prime_sixtyEightBN_73907 : Nat.Prime 73907 := by norm_num
private theorem prime_sixtyEightBN_74353 : Nat.Prime 74353 := by norm_num
private theorem prime_sixtyEightBN_77171 : Nat.Prime 77171 := by norm_num
private theorem prime_sixtyEightBN_82889 : Nat.Prime 82889 := by norm_num
private theorem prime_sixtyEightBN_83717 : Nat.Prime 83717 := by norm_num
private theorem prime_sixtyEightBN_84691 : Nat.Prime 84691 := by norm_num
private theorem prime_sixtyEightBN_85889 : Nat.Prime 85889 := by norm_num
private theorem prime_sixtyEightBN_86743 : Nat.Prime 86743 := by norm_num
private theorem prime_sixtyEightBN_89123 : Nat.Prime 89123 := by norm_num
private theorem prime_sixtyEightBN_89963 : Nat.Prime 89963 := by norm_num
private theorem prime_sixtyEightBN_92899 : Nat.Prime 92899 := by norm_num
private theorem prime_sixtyEightBN_96097 : Nat.Prime 96097 := by norm_num
private theorem prime_sixtyEightBN_99191 : Nat.Prime 99191 := by norm_num
private theorem prime_sixtyEightBN_101429 : Nat.Prime 101429 := by norm_num
private theorem prime_sixtyEightBN_109211 : Nat.Prime 109211 := by norm_num
private theorem prime_sixtyEightBN_116981 : Nat.Prime 116981 := by norm_num
private theorem prime_sixtyEightBN_122299 : Nat.Prime 122299 := by norm_num
private theorem prime_sixtyEightBN_123829 : Nat.Prime 123829 := by norm_num
private theorem prime_sixtyEightBN_131849 : Nat.Prime 131849 := by norm_num
private theorem prime_sixtyEightBN_133571 : Nat.Prime 133571 := by norm_num
private theorem prime_sixtyEightBN_134753 : Nat.Prime 134753 := by norm_num
private theorem prime_sixtyEightBN_136501 : Nat.Prime 136501 := by norm_num
private theorem prime_sixtyEightBN_137447 : Nat.Prime 137447 := by norm_num
private theorem prime_sixtyEightBN_137507 : Nat.Prime 137507 := by norm_num
private theorem prime_sixtyEightBN_139663 : Nat.Prime 139663 := by norm_num
private theorem prime_sixtyEightBN_141637 : Nat.Prime 141637 := by norm_num
private theorem prime_sixtyEightBN_145069 : Nat.Prime 145069 := by norm_num
private theorem prime_sixtyEightBN_155153 : Nat.Prime 155153 := by norm_num
private theorem prime_sixtyEightBN_162059 : Nat.Prime 162059 := by norm_num
private theorem prime_sixtyEightBN_162821 : Nat.Prime 162821 := by norm_num
private theorem prime_sixtyEightBN_166679 : Nat.Prime 166679 := by norm_num
private theorem prime_sixtyEightBN_178951 : Nat.Prime 178951 := by norm_num
private theorem prime_sixtyEightBN_181283 : Nat.Prime 181283 := by norm_num
private theorem prime_sixtyEightBN_210233 : Nat.Prime 210233 := by norm_num
private theorem prime_sixtyEightBN_218651 : Nat.Prime 218651 := by norm_num
private theorem prime_sixtyEightBN_224449 : Nat.Prime 224449 := by norm_num
private theorem prime_sixtyEightBN_224977 : Nat.Prime 224977 := by norm_num
private theorem prime_sixtyEightBN_229639 : Nat.Prime 229639 := by norm_num
private theorem prime_sixtyEightBN_260081 : Nat.Prime 260081 := by norm_num
private theorem prime_sixtyEightBN_282713 : Nat.Prime 282713 := by norm_num
private theorem prime_sixtyEightBN_289669 : Nat.Prime 289669 := by norm_num
private theorem prime_sixtyEightBN_300869 : Nat.Prime 300869 := by norm_num
private theorem prime_sixtyEightBN_303283 : Nat.Prime 303283 := by norm_num
private theorem prime_sixtyEightBN_320767 : Nat.Prime 320767 := by norm_num
private theorem prime_sixtyEightBN_322891 : Nat.Prime 322891 := by norm_num
private theorem prime_sixtyEightBN_326323 : Nat.Prime 326323 := by norm_num
private theorem prime_sixtyEightBN_341203 : Nat.Prime 341203 := by norm_num
private theorem prime_sixtyEightBN_342061 : Nat.Prime 342061 := by norm_num
private theorem prime_sixtyEightBN_344797 : Nat.Prime 344797 := by norm_num
private theorem prime_sixtyEightBN_358711 : Nat.Prime 358711 := by norm_num
private theorem prime_sixtyEightBN_366997 : Nat.Prime 366997 := by norm_num
private theorem prime_sixtyEightBN_371639 : Nat.Prime 371639 := by norm_num
private theorem prime_sixtyEightBN_390421 : Nat.Prime 390421 := by norm_num
private theorem prime_sixtyEightBN_401827 : Nat.Prime 401827 := by norm_num
private theorem prime_sixtyEightBN_404837 : Nat.Prime 404837 := by norm_num
private theorem prime_sixtyEightBN_415097 : Nat.Prime 415097 := by norm_num
private theorem prime_sixtyEightBN_435593 : Nat.Prime 435593 := by norm_num
private theorem prime_sixtyEightBN_468581 : Nat.Prime 468581 := by norm_num
private theorem prime_sixtyEightBN_475997 : Nat.Prime 475997 := by norm_num
private theorem prime_sixtyEightBN_499661 : Nat.Prime 499661 := by norm_num
private theorem prime_sixtyEightBN_509843 : Nat.Prime 509843 := by norm_num
private theorem prime_sixtyEightBN_511211 : Nat.Prime 511211 := by norm_num
private theorem prime_sixtyEightBN_512891 : Nat.Prime 512891 := by norm_num
private theorem prime_sixtyEightBN_514841 : Nat.Prime 514841 := by norm_num
private theorem prime_sixtyEightBN_522719 : Nat.Prime 522719 := by norm_num
private theorem prime_sixtyEightBN_541181 : Nat.Prime 541181 := by norm_num
private theorem prime_sixtyEightBN_550951 : Nat.Prime 550951 := by norm_num
private theorem prime_sixtyEightBN_568019 : Nat.Prime 568019 := by norm_num
private theorem prime_sixtyEightBN_578203 : Nat.Prime 578203 := by norm_num
private theorem prime_sixtyEightBN_619027 : Nat.Prime 619027 := by norm_num
private theorem prime_sixtyEightBN_642121 : Nat.Prime 642121 := by norm_num
private theorem prime_sixtyEightBN_649381 : Nat.Prime 649381 := by norm_num
private theorem prime_sixtyEightBN_687061 : Nat.Prime 687061 := by norm_num
private theorem prime_sixtyEightBN_687389 : Nat.Prime 687389 := by norm_num
private theorem prime_sixtyEightBN_718093 : Nat.Prime 718093 := by norm_num
private theorem prime_sixtyEightBN_732841 : Nat.Prime 732841 := by norm_num
private theorem prime_sixtyEightBN_734479 : Nat.Prime 734479 := by norm_num
private theorem prime_sixtyEightBN_792821 : Nat.Prime 792821 := by norm_num
private theorem prime_sixtyEightBN_848879 : Nat.Prime 848879 := by norm_num
private theorem prime_sixtyEightBN_872671 : Nat.Prime 872671 := by norm_num
private theorem prime_sixtyEightBN_874001 : Nat.Prime 874001 := by norm_num
private theorem prime_sixtyEightBN_924281 : Nat.Prime 924281 := by norm_num
private theorem prime_sixtyEightBN_928111 : Nat.Prime 928111 := by norm_num
private theorem prime_sixtyEightBN_932221 : Nat.Prime 932221 := by norm_num
private theorem prime_sixtyEightBN_979273 : Nat.Prime 979273 := by norm_num
private theorem prime_sixtyEightBN_995369 : Nat.Prime 995369 := by norm_num
private theorem prime_sixtyEightBN_1000393 : Nat.Prime 1000393 := by norm_num
private theorem prime_sixtyEightBN_1002349 : Nat.Prime 1002349 := by norm_num
private theorem prime_sixtyEightBN_1022167 : Nat.Prime 1022167 := by norm_num
private theorem prime_sixtyEightBN_1066999 : Nat.Prime 1066999 := by norm_num
private theorem prime_sixtyEightBN_1082399 : Nat.Prime 1082399 := by norm_num
private theorem prime_sixtyEightBN_1142789 : Nat.Prime 1142789 := by norm_num
private theorem prime_sixtyEightBN_1178377 : Nat.Prime 1178377 := by norm_num
private theorem prime_sixtyEightBN_1203437 : Nat.Prime 1203437 := by norm_num
private theorem prime_sixtyEightBN_1323139 : Nat.Prime 1323139 := by norm_num
private theorem prime_sixtyEightBN_1333583 : Nat.Prime 1333583 := by norm_num
private theorem prime_sixtyEightBN_1346623 : Nat.Prime 1346623 := by norm_num
private theorem prime_sixtyEightBN_1508629 : Nat.Prime 1508629 := by norm_num
private theorem prime_sixtyEightBN_1520159 : Nat.Prime 1520159 := by norm_num
private theorem prime_sixtyEightBN_1559651 : Nat.Prime 1559651 := by norm_num
private theorem prime_sixtyEightBN_1569053 : Nat.Prime 1569053 := by norm_num
private theorem prime_sixtyEightBN_1629337 : Nat.Prime 1629337 := by norm_num
private theorem prime_sixtyEightBN_1654231 : Nat.Prime 1654231 := by norm_num
private theorem prime_sixtyEightBN_1668083 : Nat.Prime 1668083 := by norm_num
private theorem prime_sixtyEightBN_1706863 : Nat.Prime 1706863 := by norm_num
private theorem prime_sixtyEightBN_1712917 : Nat.Prime 1712917 := by norm_num
private theorem prime_sixtyEightBN_1814581 : Nat.Prime 1814581 := by norm_num
private theorem prime_sixtyEightBN_1859387 : Nat.Prime 1859387 := by norm_num
private theorem prime_sixtyEightBN_1867819 : Nat.Prime 1867819 := by norm_num
private theorem prime_sixtyEightBN_1913123 : Nat.Prime 1913123 := by norm_num
private theorem prime_sixtyEightBN_2009759 : Nat.Prime 2009759 := by norm_num
private theorem prime_sixtyEightBN_2031301 : Nat.Prime 2031301 := by norm_num
private theorem prime_sixtyEightBN_2068043 : Nat.Prime 2068043 := by norm_num
private theorem prime_sixtyEightBN_2131541 : Nat.Prime 2131541 := by norm_num
private theorem prime_sixtyEightBN_2136419 : Nat.Prime 2136419 := by norm_num
private theorem prime_sixtyEightBN_2289211 : Nat.Prime 2289211 := by norm_num
private theorem prime_sixtyEightBN_2775713 : Nat.Prime 2775713 := by norm_num
private theorem prime_sixtyEightBN_2815607 : Nat.Prime 2815607 := by norm_num
private theorem prime_sixtyEightBN_3174191 : Nat.Prime 3174191 := by norm_num
private theorem prime_sixtyEightBN_3232157 : Nat.Prime 3232157 := by norm_num
private theorem prime_sixtyEightBN_3239261 : Nat.Prime 3239261 := by norm_num
private theorem prime_sixtyEightBN_3498613 : Nat.Prime 3498613 := by norm_num
private theorem prime_sixtyEightBN_3560833 : Nat.Prime 3560833 := by norm_num
private theorem prime_sixtyEightBN_3681791 : Nat.Prime 3681791 := by norm_num
private theorem prime_sixtyEightBN_3856511 : Nat.Prime 3856511 := by norm_num
private theorem prime_sixtyEightBN_3896609 : Nat.Prime 3896609 := by norm_num
private theorem prime_sixtyEightBN_3922207 : Nat.Prime 3922207 := by norm_num
private theorem prime_sixtyEightBN_4141723 : Nat.Prime 4141723 := by norm_num
private theorem prime_sixtyEightBN_4178851 : Nat.Prime 4178851 := by norm_num
private theorem prime_sixtyEightBN_4796923 : Nat.Prime 4796923 := by norm_num
private theorem prime_sixtyEightBN_4947779 : Nat.Prime 4947779 := by norm_num
private theorem prime_sixtyEightBN_5584441 : Nat.Prime 5584441 := by norm_num
private theorem prime_sixtyEightBN_5753509 : Nat.Prime 5753509 := by norm_num
private theorem prime_sixtyEightBN_7392629 : Nat.Prime 7392629 := by norm_num
private theorem prime_sixtyEightBN_7464371 : Nat.Prime 7464371 := by norm_num
private theorem prime_sixtyEightBN_7749517 : Nat.Prime 7749517 := by norm_num
private theorem prime_sixtyEightBN_8151113 : Nat.Prime 8151113 := by norm_num
private theorem prime_sixtyEightBN_9112361 : Nat.Prime 9112361 := by norm_num
private theorem prime_sixtyEightBN_9222637 : Nat.Prime 9222637 := by norm_num
private theorem prime_sixtyEightBN_9641447 : Nat.Prime 9641447 := by norm_num
private theorem prime_sixtyEightBN_10407127 : Nat.Prime 10407127 := by norm_num
private theorem prime_sixtyEightBN_10522489 : Nat.Prime 10522489 := by norm_num
private theorem prime_sixtyEightBN_10632887 : Nat.Prime 10632887 := by norm_num
private theorem prime_sixtyEightBN_10919017 : Nat.Prime 10919017 := by norm_num
private theorem prime_sixtyEightBN_11243291 : Nat.Prime 11243291 := by norm_num
private theorem prime_sixtyEightBN_11423669 : Nat.Prime 11423669 := by norm_num
private theorem prime_sixtyEightBN_12696139 : Nat.Prime 12696139 := by norm_num
private theorem prime_sixtyEightBN_12777361 : Nat.Prime 12777361 := by norm_num
private theorem prime_sixtyEightBN_13410857 : Nat.Prime 13410857 := by norm_num
private theorem prime_sixtyEightBN_13474891 : Nat.Prime 13474891 := by norm_num
private theorem prime_sixtyEightBN_13504331 : Nat.Prime 13504331 := by norm_num
private theorem prime_sixtyEightBN_13828937 : Nat.Prime 13828937 := by norm_num
private theorem prime_sixtyEightBN_13956401 : Nat.Prime 13956401 := by norm_num
private theorem prime_sixtyEightBN_14140639 : Nat.Prime 14140639 := by norm_num
private theorem prime_sixtyEightBN_14263871 : Nat.Prime 14263871 := by norm_num
private theorem prime_sixtyEightBN_15511121 : Nat.Prime 15511121 := by norm_num
private theorem prime_sixtyEightBN_16511389 : Nat.Prime 16511389 := by norm_num
private theorem prime_sixtyEightBN_17074111 : Nat.Prime 17074111 := by norm_num
private theorem prime_sixtyEightBN_19518449 : Nat.Prime 19518449 := by norm_num
private theorem prime_sixtyEightBN_19995439 : Nat.Prime 19995439 := by norm_num
private theorem prime_sixtyEightBN_21386347 : Nat.Prime 21386347 := by norm_num
private theorem prime_sixtyEightBN_22824497 : Nat.Prime 22824497 := by norm_num
private theorem prime_sixtyEightBN_25777363 : Nat.Prime 25777363 := by norm_num
private theorem prime_sixtyEightBN_29571383 : Nat.Prime 29571383 := by norm_num
private theorem prime_sixtyEightBN_29835227 : Nat.Prime 29835227 := by norm_num
private theorem prime_sixtyEightBN_31363141 : Nat.Prime 31363141 := by
  apply lucas_primality 31363141 (6 : ZMod 31363141)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (522719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (522719, 1)] : List FactorBlock).map factorBlockValue).prod) = 31363141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_522719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 31363141) ^ 15681570 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 31363141) ^ 10454380 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 31363141) ^ 6272628 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 31363141) ^ 60 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_32257403 : Nat.Prime 32257403 := by
  apply lucas_primality 32257403 (2 : ZMod 32257403)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (848879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (848879, 1)] : List FactorBlock).map factorBlockValue).prod) = 32257403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_848879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32257403) ^ 16128701 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32257403) ^ 1697758 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 32257403) ^ 38 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_33957757 : Nat.Prime 33957757 := by
  apply lucas_primality 33957757 (5 : ZMod 33957757)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (134753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (134753, 1)] : List FactorBlock).map factorBlockValue).prod) = 33957757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_134753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33957757) ^ 16978878 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 33957757) ^ 11319252 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 33957757) ^ 4851108 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 33957757) ^ 252 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_39142139 : Nat.Prime 39142139 := by
  apply lucas_primality 39142139 (2 : ZMod 39142139)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (487, 1), (5741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (487, 1), (5741, 1)] : List FactorBlock).map factorBlockValue).prod) = 39142139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_487
      · exact prime_sixtyEightBN_5741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39142139) ^ 19571069 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 39142139) ^ 5591734 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 39142139) ^ 80374 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 39142139) ^ 6818 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_39632497 : Nat.Prime 39632497 := by
  apply lucas_primality 39632497 (5 : ZMod 39632497)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (35899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (35899, 1)] : List FactorBlock).map factorBlockValue).prod) = 39632497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_35899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39632497) ^ 19816248 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 39632497) ^ 13210832 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 39632497) ^ 1723152 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 39632497) ^ 1104 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_40694077 : Nat.Prime 40694077 := by
  apply lucas_primality 40694077 (2 : ZMod 40694077)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (29, 1), (61, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (29, 1), (61, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) = 40694077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_29
      · exact prime_sixtyEightBN_61
      · exact prime_sixtyEightBN_71
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40694077) ^ 20347038 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40694077) ^ 13564692 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40694077) ^ 1403244 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40694077) ^ 667116 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40694077) ^ 573156 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_42364481 : Nat.Prime 42364481 := by
  apply lucas_primality 42364481 (3 : ZMod 42364481)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (41, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (41, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 42364481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_41
      · exact prime_sixtyEightBN_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42364481) ^ 21182240 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42364481) ^ 8472896 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42364481) ^ 1033280 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 42364481) ^ 13120 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_43128973 : Nat.Prime 43128973 := by
  apply lucas_primality 43128973 (5 : ZMod 43128973)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (17881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (17881, 1)] : List FactorBlock).map factorBlockValue).prod) = 43128973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_67
      · exact prime_sixtyEightBN_17881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43128973) ^ 21564486 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 43128973) ^ 14376324 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 43128973) ^ 643716 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 43128973) ^ 2412 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_45128929 : Nat.Prime 45128929 := by
  apply lucas_primality 45128929 (11 : ZMod 45128929)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (36161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (36161, 1)] : List FactorBlock).map factorBlockValue).prod) = 45128929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_36161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 45128929) ^ 22564464 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 45128929) ^ 15042976 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 45128929) ^ 3471456 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 45128929) ^ 1248 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_47969231 : Nat.Prime 47969231 := by
  apply lucas_primality 47969231 (7 : ZMod 47969231)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4796923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4796923, 1)] : List FactorBlock).map factorBlockValue).prod) = 47969231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_4796923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 47969231) ^ 23984615 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 47969231) ^ 9593846 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 47969231) ^ 10 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_52302223 : Nat.Prime 52302223 := by
  apply lucas_primality 52302223 (3 : ZMod 52302223)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (415097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (415097, 1)] : List FactorBlock).map factorBlockValue).prod) = 52302223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_415097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 52302223) ^ 26151111 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52302223) ^ 17434074 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52302223) ^ 7471746 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52302223) ^ 126 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_57535091 : Nat.Prime 57535091 := by
  apply lucas_primality 57535091 (2 : ZMod 57535091)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5753509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5753509, 1)] : List FactorBlock).map factorBlockValue).prod) = 57535091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_5753509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57535091) ^ 28767545 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 57535091) ^ 11507018 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 57535091) ^ 10 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_59140531 : Nat.Prime 59140531 := by
  apply lucas_primality 59140531 (2 : ZMod 59140531)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (73013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (73013, 1)] : List FactorBlock).map factorBlockValue).prod) = 59140531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_73013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59140531) ^ 29570265 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59140531) ^ 19713510 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59140531) ^ 11828106 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59140531) ^ 810 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_59344907 : Nat.Prime 59344907 := by
  apply lucas_primality 59344907 (2 : ZMod 59344907)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4259, 1), (6967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4259, 1), (6967, 1)] : List FactorBlock).map factorBlockValue).prod) = 59344907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_4259
      · exact prime_sixtyEightBN_6967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59344907) ^ 29672453 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59344907) ^ 13934 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 59344907) ^ 8518 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_71449507 : Nat.Prime 71449507 := by
  apply lucas_primality 71449507 (3 : ZMod 71449507)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1323139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1323139, 1)] : List FactorBlock).map factorBlockValue).prod) = 71449507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_1323139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71449507) ^ 35724753 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 71449507) ^ 23816502 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 71449507) ^ 54 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_72207133 : Nat.Prime 72207133 := by
  apply lucas_primality 72207133 (2 : ZMod 72207133)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (269, 1), (22369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (269, 1), (22369, 1)] : List FactorBlock).map factorBlockValue).prod) = 72207133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_269
      · exact prime_sixtyEightBN_22369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72207133) ^ 36103566 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 72207133) ^ 24069044 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 72207133) ^ 268428 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 72207133) ^ 3228 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_75421289 : Nat.Prime 75421289 := by
  apply lucas_primality 75421289 (3 : ZMod 75421289)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (599, 1), (15739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (599, 1), (15739, 1)] : List FactorBlock).map factorBlockValue).prod) = 75421289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_599
      · exact prime_sixtyEightBN_15739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 75421289) ^ 37710644 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 75421289) ^ 125912 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 75421289) ^ 4792 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_76245313 : Nat.Prime 76245313 := by
  apply lucas_primality 76245313 (5 : ZMod 76245313)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (13, 1), (2777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (13, 1), (2777, 1)] : List FactorBlock).map factorBlockValue).prod) = 76245313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_2777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76245313) ^ 38122656 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 76245313) ^ 25415104 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 76245313) ^ 6931392 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 76245313) ^ 5865024 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 76245313) ^ 27456 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_77131577 : Nat.Prime 77131577 := by
  apply lucas_primality 77131577 (3 : ZMod 77131577)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9641447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9641447, 1)] : List FactorBlock).map factorBlockValue).prod) = 77131577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_9641447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 77131577) ^ 38565788 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 77131577) ^ 8 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_77345747 : Nat.Prime 77345747 := by
  apply lucas_primality 77345747 (2 : ZMod 77345747)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (197, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (197, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) = 77345747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_109
      · exact prime_sixtyEightBN_197
      · exact prime_sixtyEightBN_1801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77345747) ^ 38672873 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 77345747) ^ 709594 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 77345747) ^ 392618 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 77345747) ^ 42946 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_79576271 : Nat.Prime 79576271 := by
  apply lucas_primality 79576271 (11 : ZMod 79576271)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (449, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (449, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 79576271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_449
      · exact prime_sixtyEightBN_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 79576271) ^ 39788135 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 79576271) ^ 15915254 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 79576271) ^ 2150710 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 79576271) ^ 177230 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 79576271) ^ 166130 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_82268581 : Nat.Prime 82268581 := by
  apply lucas_primality 82268581 (7 : ZMod 82268581)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (239, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (239, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) = 82268581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_239
      · exact prime_sixtyEightBN_5737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 82268581) ^ 41134290 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 82268581) ^ 27422860 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 82268581) ^ 16453716 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 82268581) ^ 344220 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 82268581) ^ 14340 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_89572453 : Nat.Prime 89572453 := by
  apply lucas_primality 89572453 (2 : ZMod 89572453)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7464371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7464371, 1)] : List FactorBlock).map factorBlockValue).prod) = 89572453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7464371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 89572453) ^ 44786226 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 89572453) ^ 29857484 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 89572453) ^ 12 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_91423121 : Nat.Prime 91423121 := by
  apply lucas_primality 91423121 (3 : ZMod 91423121)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1142789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1142789, 1)] : List FactorBlock).map factorBlockValue).prod) = 91423121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_1142789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 91423121) ^ 45711560 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 91423121) ^ 18284624 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 91423121) ^ 80 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_93315149 : Nat.Prime 93315149 := by
  apply lucas_primality 93315149 (2 : ZMod 93315149)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (157, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (157, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 93315149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_139
      · exact prime_sixtyEightBN_157
      · exact prime_sixtyEightBN_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93315149) ^ 46657574 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 93315149) ^ 671332 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 93315149) ^ 594364 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 93315149) ^ 87292 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_112395461 : Nat.Prime 112395461 := by
  apply lucas_primality 112395461 (2 : ZMod 112395461)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (181283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (181283, 1)] : List FactorBlock).map factorBlockValue).prod) = 112395461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_31
      · exact prime_sixtyEightBN_181283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 112395461) ^ 56197730 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 112395461) ^ 22479092 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 112395461) ^ 3625660 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 112395461) ^ 620 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_116143793 : Nat.Prime 116143793 := by
  apply lucas_primality 116143793 (3 : ZMod 116143793)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (179, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (179, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 116143793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_107
      · exact prime_sixtyEightBN_179
      · exact prime_sixtyEightBN_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 116143793) ^ 58071896 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 116143793) ^ 1085456 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 116143793) ^ 648848 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 116143793) ^ 306448 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_129854089 : Nat.Prime 129854089 := by
  apply lucas_primality 129854089 (11 : ZMod 129854089)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (13, 1), (19819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (13, 1), (19819, 1)] : List FactorBlock).map factorBlockValue).prod) = 129854089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_19819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 129854089) ^ 64927044 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 129854089) ^ 43284696 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 129854089) ^ 18550584 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 129854089) ^ 9988776 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 129854089) ^ 6552 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_131581883 : Nat.Prime 131581883 := by
  apply lucas_primality 131581883 (2 : ZMod 131581883)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (271, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (271, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) = 131581883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_103
      · exact prime_sixtyEightBN_271
      · exact prime_sixtyEightBN_2357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 131581883) ^ 65790941 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131581883) ^ 1277494 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131581883) ^ 485542 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131581883) ^ 55826 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_135849001 : Nat.Prime 135849001 := by
  apply lucas_primality 135849001 (11 : ZMod 135849001)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (7, 1), (6469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (7, 1), (6469, 1)] : List FactorBlock).map factorBlockValue).prod) = 135849001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_6469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 135849001) ^ 67924500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 135849001) ^ 45283000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 135849001) ^ 27169800 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 135849001) ^ 19407000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 135849001) ^ 21000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_139627361 : Nat.Prime 139627361 := by
  apply lucas_primality 139627361 (6 : ZMod 139627361)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (872671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (872671, 1)] : List FactorBlock).map factorBlockValue).prod) = 139627361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_872671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 139627361) ^ 69813680 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 139627361) ^ 27925472 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 139627361) ^ 160 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_144272533 : Nat.Prime 144272533 := by
  apply lucas_primality 144272533 (2 : ZMod 144272533)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (967, 1), (12433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (967, 1), (12433, 1)] : List FactorBlock).map factorBlockValue).prod) = 144272533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_967
      · exact prime_sixtyEightBN_12433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144272533) ^ 72136266 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144272533) ^ 48090844 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144272533) ^ 149196 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 144272533) ^ 11604 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_147962471 : Nat.Prime 147962471 := by
  apply lucas_primality 147962471 (19 : ZMod 147962471)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (199, 1), (74353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (199, 1), (74353, 1)] : List FactorBlock).map factorBlockValue).prod) = 147962471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_199
      · exact prime_sixtyEightBN_74353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 147962471) ^ 73981235 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 147962471) ^ 29592494 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 147962471) ^ 743530 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 147962471) ^ 1990 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_148975583 : Nat.Prime 148975583 := by
  apply lucas_primality 148975583 (7 : ZMod 148975583)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (1520159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (1520159, 1)] : List FactorBlock).map factorBlockValue).prod) = 148975583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_1520159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 148975583) ^ 74487791 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 148975583) ^ 21282226 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 148975583) ^ 98 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_150656393 : Nat.Prime 150656393 := by
  apply lucas_primality 150656393 (3 : ZMod 150656393)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (649381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (649381, 1)] : List FactorBlock).map factorBlockValue).prod) = 150656393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_29
      · exact prime_sixtyEightBN_649381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 150656393) ^ 75328196 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 150656393) ^ 5195048 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 150656393) ^ 232 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_156757981 : Nat.Prime 156757981 := by
  apply lucas_primality 156757981 (6 : ZMod 156757981)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (137507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (137507, 1)] : List FactorBlock).map factorBlockValue).prod) = 156757981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_137507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 156757981) ^ 78378990 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 156757981) ^ 52252660 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 156757981) ^ 31351596 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 156757981) ^ 8250420 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 156757981) ^ 1140 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_163596751 : Nat.Prime 163596751 := by
  apply lucas_primality 163596751 (3 : ZMod 163596751)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (331, 1), (659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (331, 1), (659, 1)] : List FactorBlock).map factorBlockValue).prod) = 163596751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_331
      · exact prime_sixtyEightBN_659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 163596751) ^ 81798375 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 163596751) ^ 54532250 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 163596751) ^ 32719350 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 163596751) ^ 494250 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 163596751) ^ 248250 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_179011363 : Nat.Prime 179011363 := by
  apply lucas_primality 179011363 (3 : ZMod 179011363)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29835227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29835227, 1)] : List FactorBlock).map factorBlockValue).prod) = 179011363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_29835227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 179011363) ^ 89505681 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 179011363) ^ 59670454 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 179011363) ^ 6 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_223149499 : Nat.Prime 223149499 := by
  apply lucas_primality 223149499 (2 : ZMod 223149499)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (260081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (260081, 1)] : List FactorBlock).map factorBlockValue).prod) = 223149499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_260081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 223149499) ^ 111574749 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 223149499) ^ 74383166 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 223149499) ^ 20286318 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 223149499) ^ 17165346 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 223149499) ^ 858 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_230297519 : Nat.Prime 230297519 := by
  apply lucas_primality 230297519 (7 : ZMod 230297519)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (550951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (550951, 1)] : List FactorBlock).map factorBlockValue).prod) = 230297519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_550951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 230297519) ^ 115148759 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 230297519) ^ 20936138 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 230297519) ^ 12120922 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 230297519) ^ 418 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_231009743 : Nat.Prime 231009743 := by
  apply lucas_primality 231009743 (5 : ZMod 231009743)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (1022167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (1022167, 1)] : List FactorBlock).map factorBlockValue).prod) = 231009743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_113
      · exact prime_sixtyEightBN_1022167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 231009743) ^ 115504871 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 231009743) ^ 2044334 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 231009743) ^ 226 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_243910409 : Nat.Prime 243910409 := by
  apply lucas_primality 243910409 (15 : ZMod 243910409)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (263, 1), (16561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (263, 1), (16561, 1)] : List FactorBlock).map factorBlockValue).prod) = 243910409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_263
      · exact prime_sixtyEightBN_16561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 243910409) ^ 121955204 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (15 : ZMod 243910409) ^ 34844344 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (15 : ZMod 243910409) ^ 927416 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (15 : ZMod 243910409) ^ 14728 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_258672767 : Nat.Prime 258672767 := by
  apply lucas_primality 258672767 (5 : ZMod 258672767)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (511211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (511211, 1)] : List FactorBlock).map factorBlockValue).prod) = 258672767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_511211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 258672767) ^ 129336383 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 258672767) ^ 23515706 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 258672767) ^ 11246642 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 258672767) ^ 506 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_258773839 : Nat.Prime 258773839 := by
  apply lucas_primality 258773839 (3 : ZMod 258773839)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43128973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43128973, 1)] : List FactorBlock).map factorBlockValue).prod) = 258773839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_43128973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 258773839) ^ 129386919 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 258773839) ^ 86257946 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 258773839) ^ 6 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_267174959 : Nat.Prime 267174959 := by
  apply lucas_primality 267174959 (7 : ZMod 267174959)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (139, 1), (56533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (139, 1), (56533, 1)] : List FactorBlock).map factorBlockValue).prod) = 267174959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_139
      · exact prime_sixtyEightBN_56533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 267174959) ^ 133587479 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 267174959) ^ 15716174 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 267174959) ^ 1922122 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 267174959) ^ 4726 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_279128021 : Nat.Prime 279128021 := by
  apply lucas_primality 279128021 (2 : ZMod 279128021)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13956401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13956401, 1)] : List FactorBlock).map factorBlockValue).prod) = 279128021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_13956401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 279128021) ^ 139564010 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 279128021) ^ 55825604 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 279128021) ^ 20 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_282257473 : Nat.Prime 282257473 := by
  apply lucas_primality 282257473 (15 : ZMod 282257473)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (23, 2), (397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (23, 2), (397, 1)] : List FactorBlock).map factorBlockValue).prod) = 282257473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 282257473) ^ 141128736 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (15 : ZMod 282257473) ^ 94085824 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (15 : ZMod 282257473) ^ 40322496 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (15 : ZMod 282257473) ^ 12272064 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (15 : ZMod 282257473) ^ 710976 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_326375641 : Nat.Prime 326375641 := by
  apply lucas_primality 326375641 (13 : ZMod 326375641)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (71, 1), (113, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (71, 1), (113, 2)] : List FactorBlock).map factorBlockValue).prod) = 326375641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_71
      · exact prime_sixtyEightBN_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 326375641) ^ 163187820 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 326375641) ^ 108791880 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 326375641) ^ 65275128 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 326375641) ^ 4596840 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 326375641) ^ 2888280 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_336783479 : Nat.Prime 336783479 := by
  apply lucas_primality 336783479 (7 : ZMod 336783479)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (2131541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (2131541, 1)] : List FactorBlock).map factorBlockValue).prod) = 336783479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_79
      · exact prime_sixtyEightBN_2131541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 336783479) ^ 168391739 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 336783479) ^ 4263082 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 336783479) ^ 158 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_355976263 : Nat.Prime 355976263 := by
  apply lucas_primality 355976263 (5 : ZMod 355976263)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (661, 1), (9973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (661, 1), (9973, 1)] : List FactorBlock).map factorBlockValue).prod) = 355976263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_661
      · exact prime_sixtyEightBN_9973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 355976263) ^ 177988131 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 355976263) ^ 118658754 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 355976263) ^ 538542 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 355976263) ^ 35694 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_361715047 : Nat.Prime 361715047 := by
  apply lucas_primality 361715047 (5 : ZMod 361715047)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (19, 1), (89, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (19, 1), (89, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 361715047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_89
      · exact prime_sixtyEightBN_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 361715047) ^ 180857523 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 361715047) ^ 120571682 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 361715047) ^ 51673578 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 361715047) ^ 32883186 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 361715047) ^ 19037634 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 361715047) ^ 4064214 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 361715047) ^ 781242 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_537973459 : Nat.Prime 537973459 := by
  apply lucas_primality 537973459 (2 : ZMod 537973459)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (8151113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (8151113, 1)] : List FactorBlock).map factorBlockValue).prod) = 537973459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_8151113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 537973459) ^ 268986729 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 537973459) ^ 179324486 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 537973459) ^ 48906678 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 537973459) ^ 66 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_546235933 : Nat.Prime 546235933 := by
  apply lucas_primality 546235933 (2 : ZMod 546235933)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (73, 1), (56687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (73, 1), (56687, 1)] : List FactorBlock).map factorBlockValue).prod) = 546235933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_73
      · exact prime_sixtyEightBN_56687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 546235933) ^ 273117966 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 546235933) ^ 182078644 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 546235933) ^ 49657812 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 546235933) ^ 7482684 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 546235933) ^ 9636 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_618532687 : Nat.Prime 618532687 := by
  apply lucas_primality 618532687 (5 : ZMod 618532687)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (101, 1), (12601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (101, 1), (12601, 1)] : List FactorBlock).map factorBlockValue).prod) = 618532687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_101
      · exact prime_sixtyEightBN_12601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 618532687) ^ 309266343 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 618532687) ^ 206177562 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 618532687) ^ 6124086 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 618532687) ^ 49086 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_653888537 : Nat.Prime 653888537 := by
  apply lucas_primality 653888537 (3 : ZMod 653888537)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (1668083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (1668083, 1)] : List FactorBlock).map factorBlockValue).prod) = 653888537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_1668083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 653888537) ^ 326944268 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 653888537) ^ 93412648 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 653888537) ^ 392 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_685014289 : Nat.Prime 685014289 := by
  apply lucas_primality 685014289 (13 : ZMod 685014289)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (271, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (271, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) = 685014289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_271
      · exact prime_sixtyEightBN_7523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 685014289) ^ 342507144 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 685014289) ^ 228338096 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 685014289) ^ 97859184 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 685014289) ^ 2527728 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 685014289) ^ 91056 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_705364031 : Nat.Prime 705364031 := by
  apply lucas_primality 705364031 (7 : ZMod 705364031)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2269, 1), (4441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2269, 1), (4441, 1)] : List FactorBlock).map factorBlockValue).prod) = 705364031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_2269
      · exact prime_sixtyEightBN_4441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 705364031) ^ 352682015 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 705364031) ^ 141072806 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 705364031) ^ 100766290 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 705364031) ^ 310870 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 705364031) ^ 158830 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_827631523 : Nat.Prime 827631523 := by
  apply lucas_primality 827631523 (2 : ZMod 827631523)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (71, 1), (137, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (71, 1), (137, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 827631523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_29
      · exact prime_sixtyEightBN_71
      · exact prime_sixtyEightBN_137
      · exact prime_sixtyEightBN_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 827631523) ^ 413815761 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 827631523) ^ 275877174 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 827631523) ^ 28539018 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 827631523) ^ 11656782 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 827631523) ^ 6041106 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 827631523) ^ 5077494 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_914122009 : Nat.Prime 914122009 := by
  apply lucas_primality 914122009 (7 : ZMod 914122009)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (12696139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (12696139, 1)] : List FactorBlock).map factorBlockValue).prod) = 914122009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_12696139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 914122009) ^ 457061004 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 914122009) ^ 304707336 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 914122009) ^ 72 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_935155589 : Nat.Prime 935155589 := by
  apply lucas_primality 935155589 (2 : ZMod 935155589)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (1569053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (1569053, 1)] : List FactorBlock).map factorBlockValue).prod) = 935155589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_149
      · exact prime_sixtyEightBN_1569053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 935155589) ^ 467577794 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 935155589) ^ 6276212 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 935155589) ^ 596 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1051380619 : Nat.Prime 1051380619 := by
  apply lucas_primality 1051380619 (3 : ZMod 1051380619)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (9222637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (9222637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1051380619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_9222637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1051380619) ^ 525690309 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1051380619) ^ 350460206 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1051380619) ^ 55335822 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1051380619) ^ 114 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1104941063 : Nat.Prime 1104941063 := by
  apply lucas_primality 1104941063 (5 : ZMod 1104941063)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (13474891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (13474891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1104941063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_41
      · exact prime_sixtyEightBN_13474891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1104941063) ^ 552470531 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1104941063) ^ 26949782 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1104941063) ^ 82 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1227767861 : Nat.Prime 1227767861 := by
  apply lucas_primality 1227767861 (3 : ZMod 1227767861)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (823, 1), (6781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (823, 1), (6781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1227767861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_823
      · exact prime_sixtyEightBN_6781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1227767861) ^ 613883930 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1227767861) ^ 245553572 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1227767861) ^ 111615260 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1227767861) ^ 1491820 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1227767861) ^ 181060 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1320306943 : Nat.Prime 1320306943 := by
  apply lucas_primality 1320306943 (3 : ZMod 1320306943)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (2136419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (2136419, 1)] : List FactorBlock).map factorBlockValue).prod) = 1320306943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_103
      · exact prime_sixtyEightBN_2136419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1320306943) ^ 660153471 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1320306943) ^ 440102314 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1320306943) ^ 12818514 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1320306943) ^ 618 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1386058459 : Nat.Prime 1386058459 := by
  apply lucas_primality 1386058459 (3 : ZMod 1386058459)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (231009743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (231009743, 1)] : List FactorBlock).map factorBlockValue).prod) = 1386058459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_231009743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1386058459) ^ 693029229 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1386058459) ^ 462019486 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1386058459) ^ 6 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1603080397 : Nat.Prime 1603080397 := by
  apply lucas_primality 1603080397 (2 : ZMod 1603080397)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (4947779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (4947779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603080397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_4947779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1603080397) ^ 801540198 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1603080397) ^ 534360132 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1603080397) ^ 324 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1877727767 : Nat.Prime 1877727767 := by
  apply lucas_primality 1877727767 (5 : ZMod 1877727767)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (7392629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (7392629, 1)] : List FactorBlock).map factorBlockValue).prod) = 1877727767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_127
      · exact prime_sixtyEightBN_7392629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1877727767) ^ 938863883 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1877727767) ^ 14785258 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1877727767) ^ 254 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1977354131 : Nat.Prime 1977354131 := by
  apply lucas_primality 1977354131 (2 : ZMod 1977354131)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (10407127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (10407127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1977354131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_10407127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1977354131) ^ 988677065 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977354131) ^ 395470826 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977354131) ^ 104071270 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977354131) ^ 190 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1992891673 : Nat.Prime 1992891673 := by
  apply lucas_primality 1992891673 (5 : ZMod 1992891673)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (23, 1), (1203437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (23, 1), (1203437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1992891673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_1203437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1992891673) ^ 996445836 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1992891673) ^ 664297224 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1992891673) ^ 86647464 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 1992891673) ^ 1656 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2023118299 : Nat.Prime 2023118299 := by
  apply lucas_primality 2023118299 (2 : ZMod 2023118299)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (112395461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (112395461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2023118299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_112395461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2023118299) ^ 1011559149 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2023118299) ^ 674372766 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2023118299) ^ 18 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2283843799 : Nat.Prime 2283843799 := by
  apply lucas_primality 2283843799 (3 : ZMod 2283843799)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (199, 1), (281, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (199, 1), (281, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2283843799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_199
      · exact prime_sixtyEightBN_281
      · exact prime_sixtyEightBN_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2283843799) ^ 1141921899 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283843799) ^ 761281266 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283843799) ^ 11476602 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283843799) ^ 8127558 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2283843799) ^ 1006542 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2572518241 : Nat.Prime 2572518241 := by
  apply lucas_primality 2572518241 (11 : ZMod 2572518241)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (37, 1), (53, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (37, 1), (53, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 2572518241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_53
      · exact prime_sixtyEightBN_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2572518241) ^ 1286259120 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2572518241) ^ 857506080 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2572518241) ^ 514503648 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2572518241) ^ 69527520 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2572518241) ^ 48538080 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 2572518241) ^ 2823840 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2752123753 : Nat.Prime 2752123753 := by
  apply lucas_primality 2752123753 (10 : ZMod 2752123753)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (433, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (433, 1), (12611, 1)] : List FactorBlock).map factorBlockValue).prod) = 2752123753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_433
      · exact prime_sixtyEightBN_12611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2752123753) ^ 1376061876 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2752123753) ^ 917374584 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2752123753) ^ 393160536 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2752123753) ^ 6355944 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 2752123753) ^ 218232 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2765930977 : Nat.Prime 2765930977 := by
  apply lucas_primality 2765930977 (7 : ZMod 2765930977)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 6), (139, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 6), (139, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 2765930977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_139
      · exact prime_sixtyEightBN_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2765930977) ^ 1382965488 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2765930977) ^ 921976992 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2765930977) ^ 19898784 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 2765930977) ^ 3242592 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2976165209 : Nat.Prime 2976165209 := by
  apply lucas_primality 2976165209 (3 : ZMod 2976165209)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (1259, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (1259, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) = 2976165209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_1259
      · exact prime_sixtyEightBN_6287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2976165209) ^ 1488082604 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2976165209) ^ 63322664 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2976165209) ^ 2363912 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 2976165209) ^ 473384 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3012207799 : Nat.Prime 3012207799 := by
  apply lucas_primality 3012207799 (6 : ZMod 3012207799)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1171, 1), (25219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1171, 1), (25219, 1)] : List FactorBlock).map factorBlockValue).prod) = 3012207799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_1171
      · exact prime_sixtyEightBN_25219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3012207799) ^ 1506103899 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3012207799) ^ 1004069266 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3012207799) ^ 177188694 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3012207799) ^ 2572338 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3012207799) ^ 119442 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3197621377 : Nat.Prime 3197621377 := by
  apply lucas_primality 3197621377 (5 : ZMod 3197621377)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (2775713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (2775713, 1)] : List FactorBlock).map factorBlockValue).prod) = 3197621377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_2775713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3197621377) ^ 1598810688 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3197621377) ^ 1065873792 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3197621377) ^ 1152 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3402611917 : Nat.Prime 3402611917 := by
  apply lucas_primality 3402611917 (6 : ZMod 3402611917)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (25777363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (25777363, 1)] : List FactorBlock).map factorBlockValue).prod) = 3402611917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_25777363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3402611917) ^ 1701305958 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3402611917) ^ 1134203972 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3402611917) ^ 309328356 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3402611917) ^ 132 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3715082599 : Nat.Prime 3715082599 := by
  apply lucas_primality 3715082599 (6 : ZMod 3715082599)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (79, 1), (116981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (79, 1), (116981, 1)] : List FactorBlock).map factorBlockValue).prod) = 3715082599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_67
      · exact prime_sixtyEightBN_79
      · exact prime_sixtyEightBN_116981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3715082599) ^ 1857541299 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3715082599) ^ 1238360866 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3715082599) ^ 55448994 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3715082599) ^ 47026362 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 3715082599) ^ 31758 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3781097479 : Nat.Prime 3781097479 := by
  apply lucas_primality 3781097479 (3 : ZMod 3781097479)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4241, 1), (49531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4241, 1), (49531, 1)] : List FactorBlock).map factorBlockValue).prod) = 3781097479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_4241
      · exact prime_sixtyEightBN_49531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3781097479) ^ 1890548739 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3781097479) ^ 1260365826 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3781097479) ^ 891558 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3781097479) ^ 76338 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4071096371 : Nat.Prime 4071096371 := by
  apply lucas_primality 4071096371 (2 : ZMod 4071096371)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (23, 1), (84691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (23, 1), (84691, 1)] : List FactorBlock).map factorBlockValue).prod) = 4071096371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_84691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4071096371) ^ 2035548185 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4071096371) ^ 814219274 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4071096371) ^ 370099670 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4071096371) ^ 214268230 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4071096371) ^ 177004190 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4071096371) ^ 48070 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4468075553 : Nat.Prime 4468075553 := by
  apply lucas_primality 4468075553 (3 : ZMod 4468075553)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (139627361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (139627361, 1)] : List FactorBlock).map factorBlockValue).prod) = 4468075553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_139627361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4468075553) ^ 2234037776 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 4468075553) ^ 32 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4883289241 : Nat.Prime 4883289241 := by
  apply lucas_primality 4883289241 (7 : ZMod 4883289241)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (40694077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (40694077, 1)] : List FactorBlock).map factorBlockValue).prod) = 4883289241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_40694077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4883289241) ^ 2441644620 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4883289241) ^ 1627763080 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4883289241) ^ 976657848 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 4883289241) ^ 120 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_5582560421 : Nat.Prime 5582560421 := by
  apply lucas_primality 5582560421 (2 : ZMod 5582560421)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (279128021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (279128021, 1)] : List FactorBlock).map factorBlockValue).prod) = 5582560421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_279128021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5582560421) ^ 2791280210 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5582560421) ^ 1116512084 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 5582560421) ^ 20 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_6889289779 : Nat.Prime 6889289779 := by
  apply lucas_primality 6889289779 (10 : ZMod 6889289779)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (41, 1), (1333583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (41, 1), (1333583, 1)] : List FactorBlock).map factorBlockValue).prod) = 6889289779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_41
      · exact prime_sixtyEightBN_1333583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6889289779) ^ 3444644889 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889289779) ^ 2296429926 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889289779) ^ 984184254 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889289779) ^ 168031458 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889289779) ^ 5166 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_7817581039 : Nat.Prime 7817581039 := by
  apply lucas_primality 7817581039 (3 : ZMod 7817581039)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (67, 1), (79, 1), (6653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (67, 1), (79, 1), (6653, 1)] : List FactorBlock).map factorBlockValue).prod) = 7817581039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_67
      · exact prime_sixtyEightBN_79
      · exact prime_sixtyEightBN_6653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7817581039) ^ 3908790519 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7817581039) ^ 2605860346 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7817581039) ^ 211285974 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7817581039) ^ 116680314 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7817581039) ^ 98956722 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 7817581039) ^ 1175046 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_7905368309 : Nat.Prime 7905368309 := by
  apply lucas_primality 7905368309 (2 : ZMod 7905368309)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (10919017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (10919017, 1)] : List FactorBlock).map factorBlockValue).prod) = 7905368309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_181
      · exact prime_sixtyEightBN_10919017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7905368309) ^ 3952684154 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7905368309) ^ 43676068 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7905368309) ^ 724 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_8813047247 : Nat.Prime 8813047247 := by
  apply lucas_primality 8813047247 (5 : ZMod 8813047247)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (167, 1), (371639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (167, 1), (371639, 1)] : List FactorBlock).map factorBlockValue).prod) = 8813047247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_71
      · exact prime_sixtyEightBN_167
      · exact prime_sixtyEightBN_371639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8813047247) ^ 4406523623 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 8813047247) ^ 124127426 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 8813047247) ^ 52772738 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 8813047247) ^ 23714 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_8938126339 : Nat.Prime 8938126339 := by
  apply lucas_primality 8938126339 (2 : ZMod 8938126339)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (773, 1), (101429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (773, 1), (101429, 1)] : List FactorBlock).map factorBlockValue).prod) = 8938126339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_773
      · exact prime_sixtyEightBN_101429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8938126339) ^ 4469063169 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8938126339) ^ 2979375446 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8938126339) ^ 470427702 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8938126339) ^ 11562906 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8938126339) ^ 88122 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_9144884603 : Nat.Prime 9144884603 := by
  apply lucas_primality 9144884603 (2 : ZMod 9144884603)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (93315149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (93315149, 1)] : List FactorBlock).map factorBlockValue).prod) = 9144884603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_93315149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9144884603) ^ 4572442301 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9144884603) ^ 1306412086 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 9144884603) ^ 98 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_9238183399 : Nat.Prime 9238183399 := by
  apply lucas_primality 9238183399 (3 : ZMod 9238183399)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (521, 1), (613, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (521, 1), (613, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) = 9238183399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_521
      · exact prime_sixtyEightBN_613
      · exact prime_sixtyEightBN_1607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9238183399) ^ 4619091699 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9238183399) ^ 3079394466 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9238183399) ^ 17731638 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9238183399) ^ 15070446 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9238183399) ^ 5748714 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_11199682621 : Nat.Prime 11199682621 := by
  apply lucas_primality 11199682621 (2 : ZMod 11199682621)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (17, 1), (19, 1), (9173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (17, 1), (19, 1), (9173, 1)] : List FactorBlock).map factorBlockValue).prod) = 11199682621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_9173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11199682621) ^ 5599841310 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11199682621) ^ 3733227540 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11199682621) ^ 2239936524 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11199682621) ^ 1599954660 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11199682621) ^ 658804860 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11199682621) ^ 589456980 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11199682621) ^ 1220940 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_11698403371 : Nat.Prime 11698403371 := by
  apply lucas_primality 11698403371 (2 : ZMod 11698403371)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (151, 1), (211, 1), (12239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (151, 1), (211, 1), (12239, 1)] : List FactorBlock).map factorBlockValue).prod) = 11698403371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_151
      · exact prime_sixtyEightBN_211
      · exact prime_sixtyEightBN_12239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11698403371) ^ 5849201685 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11698403371) ^ 3899467790 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11698403371) ^ 2339680674 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11698403371) ^ 77472870 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11698403371) ^ 55442670 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 11698403371) ^ 955830 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_13021741693 : Nat.Prime 13021741693 := by
  apply lucas_primality 13021741693 (2 : ZMod 13021741693)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (361715047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (361715047, 1)] : List FactorBlock).map factorBlockValue).prod) = 13021741693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_361715047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13021741693) ^ 6510870846 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13021741693) ^ 4340580564 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 13021741693) ^ 36 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_13453624601 : Nat.Prime 13453624601 := by
  apply lucas_primality 13453624601 (3 : ZMod 13453624601)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (23, 1), (224977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (23, 1), (224977, 1)] : List FactorBlock).map factorBlockValue).prod) = 13453624601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_224977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13453624601) ^ 6726812300 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 13453624601) ^ 2690724920 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 13453624601) ^ 1034894200 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 13453624601) ^ 584940200 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 13453624601) ^ 59800 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_13529065177 : Nat.Prime 13529065177 := by
  apply lucas_primality 13529065177 (10 : ZMod 13529065177)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (11, 2), (109, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (11, 2), (109, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) = 13529065177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_109
      · exact prime_sixtyEightBN_1583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13529065177) ^ 6764532588 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 13529065177) ^ 4509688392 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 13529065177) ^ 1229915016 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 13529065177) ^ 124119864 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 13529065177) ^ 8546472 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_14655956933 : Nat.Prime 14655956933 := by
  apply lucas_primality 14655956933 (2 : ZMod 14655956933)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (1523, 1), (23357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (1523, 1), (23357, 1)] : List FactorBlock).map factorBlockValue).prod) = 14655956933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_103
      · exact prime_sixtyEightBN_1523
      · exact prime_sixtyEightBN_23357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14655956933) ^ 7327978466 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14655956933) ^ 142290844 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14655956933) ^ 9623084 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14655956933) ^ 627476 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_15810736619 : Nat.Prime 15810736619 := by
  apply lucas_primality 15810736619 (2 : ZMod 15810736619)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7905368309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7905368309, 1)] : List FactorBlock).map factorBlockValue).prod) = 15810736619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7905368309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 15810736619) ^ 7905368309 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 15810736619) ^ 2 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_20564003459 : Nat.Prime 20564003459 := by
  apply lucas_primality 20564003459 (2 : ZMod 20564003459)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (967, 1), (10632887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (967, 1), (10632887, 1)] : List FactorBlock).map factorBlockValue).prod) = 20564003459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_967
      · exact prime_sixtyEightBN_10632887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20564003459) ^ 10282001729 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 20564003459) ^ 21265774 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 20564003459) ^ 1934 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_24352279531 : Nat.Prime 24352279531 := by
  apply lucas_primality 24352279531 (3 : ZMod 24352279531)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (313, 1), (1217, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (313, 1), (1217, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 24352279531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_313
      · exact prime_sixtyEightBN_1217
      · exact prime_sixtyEightBN_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24352279531) ^ 12176139765 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24352279531) ^ 8117426510 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24352279531) ^ 4870455906 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24352279531) ^ 77802810 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24352279531) ^ 20010090 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 24352279531) ^ 11427630 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_24687655633 : Nat.Prime 24687655633 := by
  apply lucas_primality 24687655633 (5 : ZMod 24687655633)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (37, 1), (514841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (37, 1), (514841, 1)] : List FactorBlock).map factorBlockValue).prod) = 24687655633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_514841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24687655633) ^ 12343827816 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 24687655633) ^ 8229218544 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 24687655633) ^ 667233936 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 24687655633) ^ 47952 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_25373756297 : Nat.Prime 25373756297 := by
  apply lucas_primality 25373756297 (3 : ZMod 25373756297)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (8093, 1), (55987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (8093, 1), (55987, 1)] : List FactorBlock).map factorBlockValue).prod) = 25373756297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_8093
      · exact prime_sixtyEightBN_55987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25373756297) ^ 12686878148 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 25373756297) ^ 3624822328 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 25373756297) ^ 3135272 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 25373756297) ^ 453208 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_25544745487 : Nat.Prime 25544745487 := by
  apply lucas_primality 25544745487 (3 : ZMod 25544745487)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (67, 1), (1629337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (67, 1), (1629337, 1)] : List FactorBlock).map factorBlockValue).prod) = 25544745487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_67
      · exact prime_sixtyEightBN_1629337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25544745487) ^ 12772372743 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 25544745487) ^ 8514915162 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 25544745487) ^ 1964980422 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 25544745487) ^ 381264858 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 25544745487) ^ 15678 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_25624427251 : Nat.Prime 25624427251 := by
  apply lucas_primality 25624427251 (13 : ZMod 25624427251)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (17, 1), (2009759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (17, 1), (2009759, 1)] : List FactorBlock).map factorBlockValue).prod) = 25624427251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_2009759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 25624427251) ^ 12812213625 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 25624427251) ^ 8541475750 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 25624427251) ^ 5124885450 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 25624427251) ^ 1507319250 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 25624427251) ^ 12750 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_26907249203 : Nat.Prime 26907249203 := by
  apply lucas_primality 26907249203 (2 : ZMod 26907249203)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13453624601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13453624601, 1)] : List FactorBlock).map factorBlockValue).prod) = 26907249203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_13453624601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 26907249203) ^ 13453624601 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26907249203) ^ 2 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_27593063767 : Nat.Prime 27593063767 := by
  apply lucas_primality 27593063767 (6 : ZMod 27593063767)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (19, 1), (109, 1), (43541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (19, 1), (109, 1), (43541, 1)] : List FactorBlock).map factorBlockValue).prod) = 27593063767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_109
      · exact prime_sixtyEightBN_43541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27593063767) ^ 13796531883 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 27593063767) ^ 9197687922 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 27593063767) ^ 1623121398 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 27593063767) ^ 1452266514 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 27593063767) ^ 253147374 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 27593063767) ^ 633726 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_27818535499 : Nat.Prime 27818535499 := by
  apply lucas_primality 27818535499 (2 : ZMod 27818535499)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (43, 1), (47, 1), (109, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (43, 1), (47, 1), (109, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 27818535499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_43
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_109
      · exact prime_sixtyEightBN_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27818535499) ^ 13909267749 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27818535499) ^ 9272845166 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27818535499) ^ 2139887346 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27818535499) ^ 646942686 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27818535499) ^ 591883734 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27818535499) ^ 255215922 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 27818535499) ^ 17182542 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_31294950881 : Nat.Prime 31294950881 := by
  apply lucas_primality 31294950881 (3 : ZMod 31294950881)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (1093, 1), (178951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (1093, 1), (178951, 1)] : List FactorBlock).map factorBlockValue).prod) = 31294950881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_1093
      · exact prime_sixtyEightBN_178951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31294950881) ^ 15647475440 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 31294950881) ^ 6258990176 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 31294950881) ^ 28632160 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 31294950881) ^ 174880 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_35025481817 : Nat.Prime 35025481817 := by
  apply lucas_primality 35025481817 (3 : ZMod 35025481817)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (336783479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (336783479, 1)] : List FactorBlock).map factorBlockValue).prod) = 35025481817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_336783479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35025481817) ^ 17512740908 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 35025481817) ^ 2694267832 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 35025481817) ^ 104 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_42992119199 : Nat.Prime 42992119199 := by
  apply lucas_primality 42992119199 (7 : ZMod 42992119199)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (337, 1), (9112361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (337, 1), (9112361, 1)] : List FactorBlock).map factorBlockValue).prod) = 42992119199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_337
      · exact prime_sixtyEightBN_9112361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42992119199) ^ 21496059599 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 42992119199) ^ 6141731314 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 42992119199) ^ 127573054 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 42992119199) ^ 4718 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_48245549587 : Nat.Prime 48245549587 := by
  apply lucas_primality 48245549587 (2 : ZMod 48245549587)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (618532687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (618532687, 1)] : List FactorBlock).map factorBlockValue).prod) = 48245549587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_618532687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48245549587) ^ 24122774793 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 48245549587) ^ 16081849862 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 48245549587) ^ 3711196122 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 48245549587) ^ 78 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_62492080771 : Nat.Prime 62492080771 := by
  apply lucas_primality 62492080771 (2 : ZMod 62492080771)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7, 1), (23, 1), (227, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7, 1), (23, 1), (227, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) = 62492080771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_227
      · exact prime_sixtyEightBN_2111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62492080771) ^ 31246040385 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62492080771) ^ 20830693590 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62492080771) ^ 12498416154 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62492080771) ^ 8927440110 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62492080771) ^ 2717046990 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62492080771) ^ 275295510 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 62492080771) ^ 29603070 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_66196661393 : Nat.Prime 66196661393 := by
  apply lucas_primality 66196661393 (3 : ZMod 66196661393)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (10597, 1), (390421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (10597, 1), (390421, 1)] : List FactorBlock).map factorBlockValue).prod) = 66196661393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_10597
      · exact prime_sixtyEightBN_390421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 66196661393) ^ 33098330696 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 66196661393) ^ 6246736 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 66196661393) ^ 169552 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_68617948871 : Nat.Prime 68617948871 := by
  apply lucas_primality 68617948871 (17 : ZMod 68617948871)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (127, 1), (257, 1), (210233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (127, 1), (257, 1), (210233, 1)] : List FactorBlock).map factorBlockValue).prod) = 68617948871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_127
      · exact prime_sixtyEightBN_257
      · exact prime_sixtyEightBN_210233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 68617948871) ^ 34308974435 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (17 : ZMod 68617948871) ^ 13723589774 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (17 : ZMod 68617948871) ^ 540298810 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (17 : ZMod 68617948871) ^ 266995910 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (17 : ZMod 68617948871) ^ 326390 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_70190420227 : Nat.Prime 70190420227 := by
  apply lucas_primality 70190420227 (2 : ZMod 70190420227)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11698403371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11698403371, 1)] : List FactorBlock).map factorBlockValue).prod) = 70190420227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11698403371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70190420227) ^ 35095210113 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70190420227) ^ 23396806742 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 70190420227) ^ 6 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_96872189779 : Nat.Prime 96872189779 := by
  apply lucas_primality 96872189779 (2 : ZMod 96872189779)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (59140531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (59140531, 1)] : List FactorBlock).map factorBlockValue).prod) = 96872189779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_59140531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 96872189779) ^ 48436094889 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 96872189779) ^ 32290729926 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 96872189779) ^ 13838884254 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 96872189779) ^ 7451706906 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 96872189779) ^ 1638 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_99745656301 : Nat.Prime 99745656301 := by
  apply lucas_primality 99745656301 (2 : ZMod 99745656301)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (1193, 1), (92899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (1193, 1), (92899, 1)] : List FactorBlock).map factorBlockValue).prod) = 99745656301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_1193
      · exact prime_sixtyEightBN_92899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 99745656301) ^ 49872828150 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 99745656301) ^ 33248552100 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 99745656301) ^ 19949131260 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 99745656301) ^ 83609100 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 99745656301) ^ 1073700 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_149787679043 : Nat.Prime 149787679043 := by
  apply lucas_primality 149787679043 (2 : ZMod 149787679043)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (1227767861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (1227767861, 1)] : List FactorBlock).map factorBlockValue).prod) = 149787679043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_61
      · exact prime_sixtyEightBN_1227767861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 149787679043) ^ 74893839521 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 149787679043) ^ 2455535722 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 149787679043) ^ 122 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_154989102071 : Nat.Prime 154989102071 := by
  apply lucas_primality 154989102071 (13 : ZMod 154989102071)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (3319, 1), (38593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (3319, 1), (38593, 1)] : List FactorBlock).map factorBlockValue).prod) = 154989102071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_3319
      · exact prime_sixtyEightBN_38593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 154989102071) ^ 77494551035 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 154989102071) ^ 30997820414 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 154989102071) ^ 14089918370 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 154989102071) ^ 46697530 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 154989102071) ^ 4015990 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_166287301183 : Nat.Prime 166287301183 := by
  apply lucas_primality 166287301183 (6 : ZMod 166287301183)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (9238183399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (9238183399, 1)] : List FactorBlock).map factorBlockValue).prod) = 166287301183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_9238183399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 166287301183) ^ 83143650591 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166287301183) ^ 55429100394 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 166287301183) ^ 18 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_215760316183 : Nat.Prime 215760316183 := by
  apply lucas_primality 215760316183 (3 : ZMod 215760316183)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9767, 1), (3681791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9767, 1), (3681791, 1)] : List FactorBlock).map factorBlockValue).prod) = 215760316183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_9767
      · exact prime_sixtyEightBN_3681791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 215760316183) ^ 107880158091 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 215760316183) ^ 71920105394 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 215760316183) ^ 22090746 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 215760316183) ^ 58602 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_219132808019 : Nat.Prime 219132808019 := by
  apply lucas_primality 219132808019 (2 : ZMod 219132808019)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (491, 1), (223149499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (491, 1), (223149499, 1)] : List FactorBlock).map factorBlockValue).prod) = 219132808019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_491
      · exact prime_sixtyEightBN_223149499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 219132808019) ^ 109566404009 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 219132808019) ^ 446298998 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 219132808019) ^ 982 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_225604120967 : Nat.Prime 225604120967 := by
  apply lucas_primality 225604120967 (7 : ZMod 225604120967)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 4), (547, 1), (85889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 4), (547, 1), (85889, 1)] : List FactorBlock).map factorBlockValue).prod) = 225604120967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_547
      · exact prime_sixtyEightBN_85889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 225604120967) ^ 112802060483 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 225604120967) ^ 32229160138 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 225604120967) ^ 412438978 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 225604120967) ^ 2626694 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_284120746733 : Nat.Prime 284120746733 := by
  apply lucas_primality 284120746733 (2 : ZMod 284120746733)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (547, 1), (129854089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (547, 1), (129854089, 1)] : List FactorBlock).map factorBlockValue).prod) = 284120746733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_547
      · exact prime_sixtyEightBN_129854089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 284120746733) ^ 142060373366 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 284120746733) ^ 519416356 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 284120746733) ^ 2188 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_465381060373 : Nat.Prime 465381060373 := by
  apply lucas_primality 465381060373 (2 : ZMod 465381060373)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (53, 1), (243910409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (53, 1), (243910409, 1)] : List FactorBlock).map factorBlockValue).prod) = 465381060373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_53
      · exact prime_sixtyEightBN_243910409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 465381060373) ^ 232690530186 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 465381060373) ^ 155127020124 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 465381060373) ^ 8780774724 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 465381060373) ^ 1908 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_541022215169 : Nat.Prime 541022215169 := by
  apply lucas_primality 541022215169 (3 : ZMod 541022215169)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (137, 1), (3856511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (137, 1), (3856511, 1)] : List FactorBlock).map factorBlockValue).prod) = 541022215169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_137
      · exact prime_sixtyEightBN_3856511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 541022215169) ^ 270511107584 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 541022215169) ^ 3949067264 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 541022215169) ^ 140288 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_776665570789 : Nat.Prime 776665570789 := by
  apply lucas_primality 776665570789 (2 : ZMod 776665570789)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (139, 1), (7559, 1), (20533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (139, 1), (7559, 1), (20533, 1)] : List FactorBlock).map factorBlockValue).prod) = 776665570789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_139
      · exact prime_sixtyEightBN_7559
      · exact prime_sixtyEightBN_20533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 776665570789) ^ 388332785394 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 776665570789) ^ 258888523596 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 776665570789) ^ 5587522092 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 776665570789) ^ 102747132 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 776665570789) ^ 37825236 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_793147297067 : Nat.Prime 793147297067 := by
  apply lucas_primality 793147297067 (2 : ZMod 793147297067)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (61, 1), (293, 1), (541181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (61, 1), (293, 1), (541181, 1)] : List FactorBlock).map factorBlockValue).prod) = 793147297067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_41
      · exact prime_sixtyEightBN_61
      · exact prime_sixtyEightBN_293
      · exact prime_sixtyEightBN_541181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 793147297067) ^ 396573648533 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 793147297067) ^ 19345056026 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 793147297067) ^ 13002414706 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 793147297067) ^ 2706987362 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 793147297067) ^ 1465586 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_952039557803 : Nat.Prime 952039557803 := by
  apply lucas_primality 952039557803 (2 : ZMod 952039557803)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (512891, 1), (928111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (512891, 1), (928111, 1)] : List FactorBlock).map factorBlockValue).prod) = 952039557803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_512891
      · exact prime_sixtyEightBN_928111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 952039557803) ^ 476019778901 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 952039557803) ^ 1856222 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 952039557803) ^ 1025782 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1025135711239 : Nat.Prime 1025135711239 := by
  apply lucas_primality 1025135711239 (6 : ZMod 1025135711239)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (109, 1), (42364481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (109, 1), (42364481, 1)] : List FactorBlock).map factorBlockValue).prod) = 1025135711239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_109
      · exact prime_sixtyEightBN_42364481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1025135711239) ^ 512567855619 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1025135711239) ^ 341711903746 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1025135711239) ^ 27706370574 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1025135711239) ^ 9404914782 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1025135711239) ^ 24198 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1069915950013 : Nat.Prime 1069915950013 := by
  apply lucas_primality 1069915950013 (6 : ZMod 1069915950013)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (13, 1), (19995439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (13, 1), (19995439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1069915950013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_19995439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1069915950013) ^ 534957975006 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069915950013) ^ 356638650004 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069915950013) ^ 152845135716 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069915950013) ^ 82301226924 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069915950013) ^ 53508 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1242411026657 : Nat.Prime 1242411026657 := by
  apply lucas_primality 1242411026657 (3 : ZMod 1242411026657)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (2283843799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (2283843799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1242411026657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_2283843799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1242411026657) ^ 621205513328 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1242411026657) ^ 73083001568 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1242411026657) ^ 544 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1353869037739 : Nat.Prime 1353869037739 := by
  apply lucas_primality 1353869037739 (2 : ZMod 1353869037739)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (23, 1), (37, 1), (101, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (23, 1), (37, 1), (101, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1353869037739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_101
      · exact prime_sixtyEightBN_5953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1353869037739) ^ 676934518869 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1353869037739) ^ 451289679246 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1353869037739) ^ 193409862534 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1353869037739) ^ 58863871206 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1353869037739) ^ 36591055074 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1353869037739) ^ 13404643938 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1353869037739) ^ 227426346 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1743738892501 : Nat.Prime 1743738892501 := by
  apply lucas_primality 1743738892501 (6 : ZMod 1743738892501)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 4), (11, 1), (47, 1), (127, 1), (3541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 4), (11, 1), (47, 1), (127, 1), (3541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1743738892501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_127
      · exact prime_sixtyEightBN_3541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1743738892501) ^ 871869446250 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1743738892501) ^ 581246297500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1743738892501) ^ 348747778500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1743738892501) ^ 158521717500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1743738892501) ^ 37100827500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1743738892501) ^ 13730227500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1743738892501) ^ 492442500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1869299407291 : Nat.Prime 1869299407291 := by
  apply lucas_primality 1869299407291 (2 : ZMod 1869299407291)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (15671, 1), (568019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (15671, 1), (568019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1869299407291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_15671
      · exact prime_sixtyEightBN_568019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1869299407291) ^ 934649703645 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869299407291) ^ 623099802430 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869299407291) ^ 373859881458 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869299407291) ^ 267042772470 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869299407291) ^ 119283990 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869299407291) ^ 3290910 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2207212919647 : Nat.Prime 2207212919647 := by
  apply lucas_primality 2207212919647 (5 : ZMod 2207212919647)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (2765930977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (2765930977, 1)] : List FactorBlock).map factorBlockValue).prod) = 2207212919647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_2765930977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2207212919647) ^ 1103606459823 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2207212919647) ^ 735737639882 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2207212919647) ^ 315316131378 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2207212919647) ^ 116169101034 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 2207212919647) ^ 798 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2923464105533 : Nat.Prime 2923464105533 := by
  apply lucas_primality 2923464105533 (2 : ZMod 2923464105533)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (42992119199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (42992119199, 1)] : List FactorBlock).map factorBlockValue).prod) = 2923464105533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_42992119199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2923464105533) ^ 1461732052766 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2923464105533) ^ 171968476796 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2923464105533) ^ 68 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3171095722603 : Nat.Prime 3171095722603 := by
  apply lucas_primality 3171095722603 (3 : ZMod 3171095722603)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (89, 1), (829, 1), (46819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (89, 1), (829, 1), (46819, 1)] : List FactorBlock).map factorBlockValue).prod) = 3171095722603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_89
      · exact prime_sixtyEightBN_829
      · exact prime_sixtyEightBN_46819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3171095722603) ^ 1585547861301 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3171095722603) ^ 1057031907534 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3171095722603) ^ 186535042506 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3171095722603) ^ 35630289018 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3171095722603) ^ 3825205938 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3171095722603) ^ 67730958 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3806063444551 : Nat.Prime 3806063444551 := by
  apply lucas_primality 3806063444551 (3 : ZMod 3806063444551)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (25373756297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (25373756297, 1)] : List FactorBlock).map factorBlockValue).prod) = 3806063444551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_25373756297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3806063444551) ^ 1903031722275 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3806063444551) ^ 1268687814850 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3806063444551) ^ 761212688910 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3806063444551) ^ 150 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4279663800053 : Nat.Prime 4279663800053 := by
  apply lucas_primality 4279663800053 (2 : ZMod 4279663800053)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1069915950013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1069915950013, 1)] : List FactorBlock).map factorBlockValue).prod) = 4279663800053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_1069915950013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4279663800053) ^ 2139831900026 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4279663800053) ^ 4 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4873868612423 : Nat.Prime 4873868612423 := by
  apply lucas_primality 4873868612423 (5 : ZMod 4873868612423)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1178377, 1), (2068043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1178377, 1), (2068043, 1)] : List FactorBlock).map factorBlockValue).prod) = 4873868612423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_1178377
      · exact prime_sixtyEightBN_2068043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4873868612423) ^ 2436934306211 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 4873868612423) ^ 4136086 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 4873868612423) ^ 2356754 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_5407271923699 : Nat.Prime 5407271923699 := by
  apply lucas_primality 5407271923699 (10 : ZMod 5407271923699)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (15810736619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (15810736619, 1)] : List FactorBlock).map factorBlockValue).prod) = 5407271923699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_15810736619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5407271923699) ^ 2703635961849 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 5407271923699) ^ 1802423974566 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 5407271923699) ^ 284593259142 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 5407271923699) ^ 342 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_5782241126089 : Nat.Prime 5782241126089 := by
  apply lucas_primality 5782241126089 (11 : ZMod 5782241126089)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (41, 1), (83, 1), (241, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (41, 1), (83, 1), (241, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5782241126089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_41
      · exact prime_sixtyEightBN_83
      · exact prime_sixtyEightBN_241
      · exact prime_sixtyEightBN_4663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5782241126089) ^ 2891120563044 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 5782241126089) ^ 1927413708696 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 5782241126089) ^ 826034446584 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 5782241126089) ^ 141030271368 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 5782241126089) ^ 69665555736 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 5782241126089) ^ 23992701768 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 5782241126089) ^ 1240025976 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_7190196242683 : Nat.Prime 7190196242683 := by
  apply lucas_primality 7190196242683 (2 : ZMod 7190196242683)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (11199682621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (11199682621, 1)] : List FactorBlock).map factorBlockValue).prod) = 7190196242683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_107
      · exact prime_sixtyEightBN_11199682621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7190196242683) ^ 3595098121341 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7190196242683) ^ 2396732080894 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7190196242683) ^ 67198095726 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7190196242683) ^ 642 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_7451797536487 : Nat.Prime 7451797536487 := by
  apply lucas_primality 7451797536487 (5 : ZMod 7451797536487)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (24352279531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (24352279531, 1)] : List FactorBlock).map factorBlockValue).prod) = 7451797536487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_24352279531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7451797536487) ^ 3725898768243 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7451797536487) ^ 2483932512162 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7451797536487) ^ 438341031558 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 7451797536487) ^ 306 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_7498446574709 : Nat.Prime 7498446574709 := by
  apply lucas_primality 7498446574709 (2 : ZMod 7498446574709)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1783, 1), (1051380619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1783, 1), (1051380619, 1)] : List FactorBlock).map factorBlockValue).prod) = 7498446574709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_1783
      · exact prime_sixtyEightBN_1051380619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7498446574709) ^ 3749223287354 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7498446574709) ^ 4205522476 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 7498446574709) ^ 7132 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_8557133267491 : Nat.Prime 8557133267491 := by
  apply lucas_primality 8557133267491 (2 : ZMod 8557133267491)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (137, 1), (15791, 1), (131849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (137, 1), (15791, 1), (131849, 1)] : List FactorBlock).map factorBlockValue).prod) = 8557133267491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_137
      · exact prime_sixtyEightBN_15791
      · exact prime_sixtyEightBN_131849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8557133267491) ^ 4278566633745 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8557133267491) ^ 2852377755830 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8557133267491) ^ 1711426653498 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8557133267491) ^ 62460826770 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8557133267491) ^ 541899390 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8557133267491) ^ 64901010 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_8900521196339 : Nat.Prime 8900521196339 := by
  apply lucas_primality 8900521196339 (2 : ZMod 8900521196339)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57697, 1), (77131577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57697, 1), (77131577, 1)] : List FactorBlock).map factorBlockValue).prod) = 8900521196339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_57697
      · exact prime_sixtyEightBN_77131577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8900521196339) ^ 4450260598169 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900521196339) ^ 154263154 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900521196339) ^ 115394 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_14186310285131 : Nat.Prime 14186310285131 := by
  apply lucas_primality 14186310285131 (2 : ZMod 14186310285131)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (41, 1), (935155589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (41, 1), (935155589, 1)] : List FactorBlock).map factorBlockValue).prod) = 14186310285131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_41
      · exact prime_sixtyEightBN_935155589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14186310285131) ^ 7093155142565 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14186310285131) ^ 2837262057026 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14186310285131) ^ 383413791490 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14186310285131) ^ 346007567930 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14186310285131) ^ 15170 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_14996893149419 : Nat.Prime 14996893149419 := by
  apply lucas_primality 14996893149419 (2 : ZMod 14996893149419)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7498446574709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7498446574709, 1)] : List FactorBlock).map factorBlockValue).prod) = 14996893149419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7498446574709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14996893149419) ^ 7498446574709 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 14996893149419) ^ 2 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_25677982800319 : Nat.Prime 25677982800319 := by
  apply lucas_primality 25677982800319 (6 : ZMod 25677982800319)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4279663800053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4279663800053, 1)] : List FactorBlock).map factorBlockValue).prod) = 25677982800319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_4279663800053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 25677982800319) ^ 12838991400159 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 25677982800319) ^ 8559327600106 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 25677982800319) ^ 6 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_25884937613641 : Nat.Prime 25884937613641 := by
  apply lucas_primality 25884937613641 (11 : ZMod 25884937613641)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (19, 1), (139, 1), (331, 1), (35251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (19, 1), (139, 1), (331, 1), (35251, 1)] : List FactorBlock).map factorBlockValue).prod) = 25884937613641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_139
      · exact prime_sixtyEightBN_331
      · exact prime_sixtyEightBN_35251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 25884937613641) ^ 12942468806820 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25884937613641) ^ 8628312537880 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25884937613641) ^ 5176987522728 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25884937613641) ^ 3697848230520 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25884937613641) ^ 1362365137560 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25884937613641) ^ 186222572760 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25884937613641) ^ 78202228440 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 25884937613641) ^ 734303640 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_27258449232647 : Nat.Prime 27258449232647 := by
  apply lucas_primality 27258449232647 (5 : ZMod 27258449232647)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (139, 1), (3217, 1), (499661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (139, 1), (3217, 1), (499661, 1)] : List FactorBlock).map factorBlockValue).prod) = 27258449232647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_61
      · exact prime_sixtyEightBN_139
      · exact prime_sixtyEightBN_3217
      · exact prime_sixtyEightBN_499661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 27258449232647) ^ 13629224616323 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 27258449232647) ^ 446859823486 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 27258449232647) ^ 196103951314 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 27258449232647) ^ 8473251238 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 27258449232647) ^ 54553886 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_28969335407581 : Nat.Prime 28969335407581 := by
  apply lucas_primality 28969335407581 (10 : ZMod 28969335407581)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (677, 1), (971, 1), (734479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (677, 1), (971, 1), (734479, 1)] : List FactorBlock).map factorBlockValue).prod) = 28969335407581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_677
      · exact prime_sixtyEightBN_971
      · exact prime_sixtyEightBN_734479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 28969335407581) ^ 14484667703790 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 28969335407581) ^ 9656445135860 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 28969335407581) ^ 5793867081516 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 28969335407581) ^ 42790746540 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 28969335407581) ^ 29834536980 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 28969335407581) ^ 39442020 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_35569032174859 : Nat.Prime 35569032174859 := by
  apply lucas_primality 35569032174859 (2 : ZMod 35569032174859)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (47, 1), (1386058459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (47, 1), (1386058459, 1)] : List FactorBlock).map factorBlockValue).prod) = 35569032174859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_1386058459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35569032174859) ^ 17784516087429 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 35569032174859) ^ 11856344058286 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 35569032174859) ^ 5081290310694 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 35569032174859) ^ 2736079398066 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 35569032174859) ^ 756787918614 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 35569032174859) ^ 25662 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_40024913188333 : Nat.Prime 40024913188333 := by
  apply lucas_primality 40024913188333 (2 : ZMod 40024913188333)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1619, 1), (89572453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1619, 1), (89572453, 1)] : List FactorBlock).map factorBlockValue).prod) = 40024913188333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_1619
      · exact prime_sixtyEightBN_89572453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40024913188333) ^ 20012456594166 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40024913188333) ^ 13341637729444 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40024913188333) ^ 1740213616884 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40024913188333) ^ 24721997028 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 40024913188333) ^ 446844 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_41606984462531 : Nat.Prime 41606984462531 := by
  apply lucas_primality 41606984462531 (2 : ZMod 41606984462531)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (300869, 1), (13828937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (300869, 1), (13828937, 1)] : List FactorBlock).map factorBlockValue).prod) = 41606984462531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_300869
      · exact prime_sixtyEightBN_13828937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41606984462531) ^ 20803492231265 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 41606984462531) ^ 8321396892506 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 41606984462531) ^ 138289370 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 41606984462531) ^ 3008690 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_49443815592023 : Nat.Prime 49443815592023 := by
  apply lucas_primality 49443815592023 (5 : ZMod 49443815592023)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (89, 1), (3257, 1), (1814581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (89, 1), (3257, 1), (1814581, 1)] : List FactorBlock).map factorBlockValue).prod) = 49443815592023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_89
      · exact prime_sixtyEightBN_3257
      · exact prime_sixtyEightBN_1814581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49443815592023) ^ 24721907796011 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49443815592023) ^ 1051996076426 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49443815592023) ^ 555548489798 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49443815592023) ^ 15180784646 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 49443815592023) ^ 27248062 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_63277966850671 : Nat.Prime 63277966850671 := by
  apply lucas_primality 63277966850671 (12 : ZMod 63277966850671)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (13, 1), (19, 1), (258773839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (13, 1), (19, 1), (258773839, 1)] : List FactorBlock).map factorBlockValue).prod) = 63277966850671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_258773839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 63277966850671) ^ 31638983425335 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (12 : ZMod 63277966850671) ^ 21092655616890 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (12 : ZMod 63277966850671) ^ 12655593370134 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (12 : ZMod 63277966850671) ^ 5752542440970 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (12 : ZMod 63277966850671) ^ 4867535911590 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (12 : ZMod 63277966850671) ^ 3330419307930 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (12 : ZMod 63277966850671) ^ 244530 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_94099895372753 : Nat.Prime 94099895372753 := by
  apply lucas_primality 94099895372753 (3 : ZMod 94099895372753)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73907, 1), (79576271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73907, 1), (79576271, 1)] : List FactorBlock).map factorBlockValue).prod) = 94099895372753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_73907
      · exact prime_sixtyEightBN_79576271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94099895372753) ^ 47049947686376 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 94099895372753) ^ 1273220336 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 94099895372753) ^ 1182512 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_112552921338863 : Nat.Prime 112552921338863 := by
  apply lucas_primality 112552921338863 (5 : ZMod 112552921338863)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (701, 1), (827631523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (701, 1), (827631523, 1)] : List FactorBlock).map factorBlockValue).prod) = 112552921338863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_97
      · exact prime_sixtyEightBN_701
      · exact prime_sixtyEightBN_827631523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 112552921338863) ^ 56276460669431 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 112552921338863) ^ 1160339395246 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 112552921338863) ^ 160560515462 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 112552921338863) ^ 135994 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_126429607184747 : Nat.Prime 126429607184747 := by
  apply lucas_primality 126429607184747 (2 : ZMod 126429607184747)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3109, 1), (6277, 1), (3239261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3109, 1), (6277, 1), (3239261, 1)] : List FactorBlock).map factorBlockValue).prod) = 126429607184747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3109
      · exact prime_sixtyEightBN_6277
      · exact prime_sixtyEightBN_3239261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126429607184747) ^ 63214803592373 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 126429607184747) ^ 40665682594 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 126429607184747) ^ 20141724898 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 126429607184747) ^ 39030386 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_155291369287723 : Nat.Prime 155291369287723 := by
  apply lucas_primality 155291369287723 (2 : ZMod 155291369287723)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37783, 1), (685014289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37783, 1), (685014289, 1)] : List FactorBlock).map factorBlockValue).prod) = 155291369287723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_37783
      · exact prime_sixtyEightBN_685014289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 155291369287723) ^ 77645684643861 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 155291369287723) ^ 51763789762574 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 155291369287723) ^ 4110085734 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 155291369287723) ^ 226698 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_296662893552139 : Nat.Prime 296662893552139 := by
  apply lucas_primality 296662893552139 (2 : ZMod 296662893552139)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (49443815592023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (49443815592023, 1)] : List FactorBlock).map factorBlockValue).prod) = 296662893552139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_49443815592023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 296662893552139) ^ 148331446776069 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 296662893552139) ^ 98887631184046 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 296662893552139) ^ 6 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_416194676596189 : Nat.Prime 416194676596189 := by
  apply lucas_primality 416194676596189 (10 : ZMod 416194676596189)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (122299, 1), (13504331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (122299, 1), (13504331, 1)] : List FactorBlock).map factorBlockValue).prod) = 416194676596189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_122299
      · exact prime_sixtyEightBN_13504331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 416194676596189) ^ 208097338298094 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 416194676596189) ^ 138731558865396 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 416194676596189) ^ 59456382370884 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 416194676596189) ^ 3403091412 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 416194676596189) ^ 30819348 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_587487334958651 : Nat.Prime 587487334958651 := by
  apply lucas_primality 587487334958651 (2 : ZMod 587487334958651)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (67, 1), (479, 1), (52302223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (67, 1), (479, 1), (52302223, 1)] : List FactorBlock).map factorBlockValue).prod) = 587487334958651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_67
      · exact prime_sixtyEightBN_479
      · exact prime_sixtyEightBN_52302223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 587487334958651) ^ 293743667479325 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 587487334958651) ^ 117497466991730 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 587487334958651) ^ 83926762136950 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 587487334958651) ^ 8768467685950 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 587487334958651) ^ 1226487129350 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 587487334958651) ^ 11232550 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_666497274005653 : Nat.Prime 666497274005653 := by
  apply lucas_primality 666497274005653 (2 : ZMod 666497274005653)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (718093, 1), (77345747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (718093, 1), (77345747, 1)] : List FactorBlock).map factorBlockValue).prod) = 666497274005653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_718093
      · exact prime_sixtyEightBN_77345747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 666497274005653) ^ 333248637002826 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 666497274005653) ^ 222165758001884 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 666497274005653) ^ 928148964 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 666497274005653) ^ 8617116 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_727095213485609 : Nat.Prime 727095213485609 := by
  apply lucas_primality 727095213485609 (3 : ZMod 727095213485609)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (53, 1), (127, 1), (72207133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (53, 1), (127, 1), (72207133, 1)] : List FactorBlock).map factorBlockValue).prod) = 727095213485609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_53
      · exact prime_sixtyEightBN_127
      · exact prime_sixtyEightBN_72207133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 727095213485609) ^ 363547606742804 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 727095213485609) ^ 66099564862328 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 727095213485609) ^ 42770306675624 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 727095213485609) ^ 13718777612936 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 727095213485609) ^ 5725159161304 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 727095213485609) ^ 10069576 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1148725965189689 : Nat.Prime 1148725965189689 := by
  apply lucas_primality 1148725965189689 (3 : ZMod 1148725965189689)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11027, 1), (13021741693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11027, 1), (13021741693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1148725965189689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_11027
      · exact prime_sixtyEightBN_13021741693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1148725965189689) ^ 574362982594844 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1148725965189689) ^ 104173933544 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1148725965189689) ^ 88216 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1683940945780339 : Nat.Prime 1683940945780339 := by
  apply lucas_primality 1683940945780339 (3 : ZMod 1683940945780339)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (251, 1), (1019, 1), (156757981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (251, 1), (1019, 1), (156757981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1683940945780339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_251
      · exact prime_sixtyEightBN_1019
      · exact prime_sixtyEightBN_156757981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1683940945780339) ^ 841970472890169 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1683940945780339) ^ 561313648593446 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1683940945780339) ^ 240562992254334 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1683940945780339) ^ 6708928070838 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1683940945780339) ^ 1652542635702 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1683940945780339) ^ 10742298 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2665989096022613 : Nat.Prime 2665989096022613 := by
  apply lucas_primality 2665989096022613 (2 : ZMod 2665989096022613)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (666497274005653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (666497274005653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2665989096022613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_666497274005653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2665989096022613) ^ 1332994548011306 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2665989096022613) ^ 4 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2822764026105293 : Nat.Prime 2822764026105293 := by
  apply lucas_primality 2822764026105293 (2 : ZMod 2822764026105293)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (13781, 1), (3012207799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (13781, 1), (3012207799, 1)] : List FactorBlock).map factorBlockValue).prod) = 2822764026105293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_13781
      · exact prime_sixtyEightBN_3012207799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2822764026105293) ^ 1411382013052646 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2822764026105293) ^ 166044942712076 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2822764026105293) ^ 204830130332 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 2822764026105293) ^ 937108 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3648000672787021 : Nat.Prime 3648000672787021 := by
  apply lucas_primality 3648000672787021 (2 : ZMod 3648000672787021)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (53, 2), (61, 1), (32257403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (53, 2), (61, 1), (32257403, 1)] : List FactorBlock).map factorBlockValue).prod) = 3648000672787021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_53
      · exact prime_sixtyEightBN_61
      · exact prime_sixtyEightBN_32257403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3648000672787021) ^ 1824000336393510 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3648000672787021) ^ 1216000224262340 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3648000672787021) ^ 729600134557404 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3648000672787021) ^ 331636424798820 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3648000672787021) ^ 68830201373340 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3648000672787021) ^ 59803289717820 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3648000672787021) ^ 113090340 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_5928223931229983 : Nat.Prime 5928223931229983 := by
  apply lucas_primality 5928223931229983 (5 : ZMod 5928223931229983)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (499, 1), (1571, 1), (3781097479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (499, 1), (1571, 1), (3781097479, 1)] : List FactorBlock).map factorBlockValue).prod) = 5928223931229983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_499
      · exact prime_sixtyEightBN_1571
      · exact prime_sixtyEightBN_3781097479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5928223931229983) ^ 2964111965614991 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5928223931229983) ^ 11880208279018 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5928223931229983) ^ 3773535284042 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 5928223931229983) ^ 1567858 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_5996712498589529 : Nat.Prime 5996712498589529 := by
  apply lucas_primality 5996712498589529 (3 : ZMod 5996712498589529)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (401, 1), (1869299407291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (401, 1), (1869299407291, 1)] : List FactorBlock).map factorBlockValue).prod) = 5996712498589529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_401
      · exact prime_sixtyEightBN_1869299407291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5996712498589529) ^ 2998356249294764 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5996712498589529) ^ 14954395258328 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 5996712498589529) ^ 3208 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_6428372446993073 : Nat.Prime 6428372446993073 := by
  apply lucas_primality 6428372446993073 (3 : ZMod 6428372446993073)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (857, 1), (24019, 1), (19518449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (857, 1), (24019, 1), (19518449, 1)] : List FactorBlock).map factorBlockValue).prod) = 6428372446993073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_857
      · exact prime_sixtyEightBN_24019
      · exact prime_sixtyEightBN_19518449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6428372446993073) ^ 3214186223496536 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6428372446993073) ^ 7501018024496 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6428372446993073) ^ 267636972688 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6428372446993073) ^ 329348528 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_6639193213441309 : Nat.Prime 6639193213441309 := by
  apply lucas_primality 6639193213441309 (2 : ZMod 6639193213441309)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (14186310285131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (14186310285131, 1)] : List FactorBlock).map factorBlockValue).prod) = 6639193213441309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_14186310285131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6639193213441309) ^ 3319596606720654 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6639193213441309) ^ 2213064404480436 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6639193213441309) ^ 510707170264716 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6639193213441309) ^ 468 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_9189807721517513 : Nat.Prime 9189807721517513 := by
  apply lucas_primality 9189807721517513 (3 : ZMod 9189807721517513)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1148725965189689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1148725965189689, 1)] : List FactorBlock).map factorBlockValue).prod) = 9189807721517513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_1148725965189689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 9189807721517513) ^ 4594903860758756 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 9189807721517513) ^ 8 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_23690923368940739 : Nat.Prime 23690923368940739 := by
  apply lucas_primality 23690923368940739 (2 : ZMod 23690923368940739)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (397, 1), (166679, 1), (179011363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (397, 1), (166679, 1), (179011363, 1)] : List FactorBlock).map factorBlockValue).prod) = 23690923368940739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_397
      · exact prime_sixtyEightBN_166679
      · exact prime_sixtyEightBN_179011363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23690923368940739) ^ 11845461684470369 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 23690923368940739) ^ 59674869946954 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 23690923368940739) ^ 142135022222 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 23690923368940739) ^ 132343126 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_28791512649353239 : Nat.Prime 28791512649353239 := by
  apply lucas_primality 28791512649353239 (3 : ZMod 28791512649353239)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (47, 1), (53, 1), (139663, 1), (320767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (47, 1), (53, 1), (139663, 1), (320767, 1)] : List FactorBlock).map factorBlockValue).prod) = 28791512649353239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_43
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_53
      · exact prime_sixtyEightBN_139663
      · exact prime_sixtyEightBN_320767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28791512649353239) ^ 14395756324676619 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28791512649353239) ^ 9597170883117746 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28791512649353239) ^ 669570061612866 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28791512649353239) ^ 612585375518154 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28791512649353239) ^ 543236087723646 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28791512649353239) ^ 206149894026 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 28791512649353239) ^ 89758337514 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_34803017560367107 : Nat.Prime 34803017560367107 := by
  apply lucas_primality 34803017560367107 (5 : ZMod 34803017560367107)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (37, 1), (56369, 1), (163596751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (37, 1), (56369, 1), (163596751, 1)] : List FactorBlock).map factorBlockValue).prod) = 34803017560367107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_56369
      · exact prime_sixtyEightBN_163596751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34803017560367107) ^ 17401508780183553 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 34803017560367107) ^ 11601005853455702 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 34803017560367107) ^ 2047236327080418 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 34803017560367107) ^ 940622096226138 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 34803017560367107) ^ 617414138274 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 34803017560367107) ^ 212736606 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_37045838689502101 : Nat.Prime 37045838689502101 := by
  apply lucas_primality 37045838689502101 (6 : ZMod 37045838689502101)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (1723, 1), (1831, 1), (39142139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (1723, 1), (1831, 1), (39142139, 1)] : List FactorBlock).map factorBlockValue).prod) = 37045838689502101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_1723
      · exact prime_sixtyEightBN_1831
      · exact prime_sixtyEightBN_39142139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37045838689502101) ^ 18522919344751050 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 37045838689502101) ^ 12348612896500700 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 37045838689502101) ^ 7409167737900420 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 37045838689502101) ^ 21500776952700 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 37045838689502101) ^ 20232571649100 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 37045838689502101) ^ 946443900 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_45484372197819431 : Nat.Prime 45484372197819431 := by
  apply lucas_primality 45484372197819431 (7 : ZMod 45484372197819431)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12777361, 1), (355976263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12777361, 1), (355976263, 1)] : List FactorBlock).map factorBlockValue).prod) = 45484372197819431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_12777361
      · exact prime_sixtyEightBN_355976263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 45484372197819431) ^ 22742186098909715 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 45484372197819431) ^ 9096874439563886 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 45484372197819431) ^ 3559762630 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 45484372197819431) ^ 127773610 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_68148530855203517 : Nat.Prime 68148530855203517 := by
  apply lucas_primality 68148530855203517 (2 : ZMod 68148530855203517)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (587487334958651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (587487334958651, 1)] : List FactorBlock).map factorBlockValue).prod) = 68148530855203517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_29
      · exact prime_sixtyEightBN_587487334958651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68148530855203517) ^ 34074265427601758 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 68148530855203517) ^ 2349949339834604 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 68148530855203517) ^ 116 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_68828813230418249 : Nat.Prime 68828813230418249 := by
  apply lucas_primality 68828813230418249 (3 : ZMod 68828813230418249)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1439, 1), (2617, 1), (326375641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1439, 1), (2617, 1), (326375641, 1)] : List FactorBlock).map factorBlockValue).prod) = 68828813230418249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_1439
      · exact prime_sixtyEightBN_2617
      · exact prime_sixtyEightBN_326375641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68828813230418249) ^ 34414406615209124 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 68828813230418249) ^ 9832687604345464 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 68828813230418249) ^ 47831002939832 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 68828813230418249) ^ 26300654654344 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 68828813230418249) ^ 210888328 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_79877419517588941 : Nat.Prime 79877419517588941 := by
  apply lucas_primality 79877419517588941 (2 : ZMod 79877419517588941)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (47, 1), (137, 1), (14779, 1), (358711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (47, 1), (137, 1), (14779, 1), (358711, 1)] : List FactorBlock).map factorBlockValue).prod) = 79877419517588941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_137
      · exact prime_sixtyEightBN_14779
      · exact prime_sixtyEightBN_358711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79877419517588941) ^ 39938709758794470 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 79877419517588941) ^ 26625806505862980 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 79877419517588941) ^ 15975483903517788 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 79877419517588941) ^ 6144416885968380 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 79877419517588941) ^ 1699519564204020 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 79877419517588941) ^ 583046857792620 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 79877419517588941) ^ 5404791901860 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 79877419517588941) ^ 222679035540 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_83526916242885721 : Nat.Prime 83526916242885721 := by
  apply lucas_primality 83526916242885721 (19 : ZMod 83526916242885721)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (63277966850671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (63277966850671, 1)] : List FactorBlock).map factorBlockValue).prod) = 83526916242885721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_63277966850671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 83526916242885721) ^ 41763458121442860 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 83526916242885721) ^ 27842305414295240 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 83526916242885721) ^ 16705383248577144 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 83526916242885721) ^ 7593356022080520 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 83526916242885721) ^ 1320 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_83890813480507741 : Nat.Prime 83890813480507741 := by
  apply lucas_primality 83890813480507741 (2 : ZMod 83890813480507741)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (73, 1), (109, 2), (230297519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (73, 1), (109, 2), (230297519, 1)] : List FactorBlock).map factorBlockValue).prod) = 83890813480507741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_73
      · exact prime_sixtyEightBN_109
      · exact prime_sixtyEightBN_230297519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83890813480507741) ^ 41945406740253870 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 83890813480507741) ^ 27963604493502580 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 83890813480507741) ^ 16778162696101548 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 83890813480507741) ^ 11984401925786820 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 83890813480507741) ^ 1149189225760380 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 83890813480507741) ^ 769640490646860 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 83890813480507741) ^ 364271460 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_101208176196524801 : Nat.Prime 101208176196524801 := by
  apply lucas_primality 101208176196524801 (7 : ZMod 101208176196524801)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (13, 1), (83, 1), (14655956933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (13, 1), (83, 1), (14655956933, 1)] : List FactorBlock).map factorBlockValue).prod) = 101208176196524801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_83
      · exact prime_sixtyEightBN_14655956933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 101208176196524801) ^ 50604088098262400 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 101208176196524801) ^ 20241635239304960 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 101208176196524801) ^ 7785244322809600 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 101208176196524801) ^ 1219375616825600 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 101208176196524801) ^ 6905600 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_131004933804314627 : Nat.Prime 131004933804314627 := by
  apply lucas_primality 131004933804314627 (2 : ZMod 131004933804314627)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (37, 1), (2917, 1), (33749, 1), (366997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (37, 1), (2917, 1), (33749, 1), (366997, 1)] : List FactorBlock).map factorBlockValue).prod) = 131004933804314627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_2917
      · exact prime_sixtyEightBN_33749
      · exact prime_sixtyEightBN_366997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131004933804314627) ^ 65502466902157313 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131004933804314627) ^ 18714990543473518 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131004933804314627) ^ 3540673886603098 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131004933804314627) ^ 44910844636378 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131004933804314627) ^ 3881742682874 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 131004933804314627) ^ 356964590458 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_132575079676415891 : Nat.Prime 132575079676415891 := by
  apply lucas_primality 132575079676415891 (2 : ZMod 132575079676415891)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3361, 1), (55207, 1), (71449507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3361, 1), (55207, 1), (71449507, 1)] : List FactorBlock).map factorBlockValue).prod) = 132575079676415891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_3361
      · exact prime_sixtyEightBN_55207
      · exact prime_sixtyEightBN_71449507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 132575079676415891) ^ 66287539838207945 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 132575079676415891) ^ 26515015935283178 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 132575079676415891) ^ 39445129329490 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 132575079676415891) ^ 2401417930270 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 132575079676415891) ^ 1855507270 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_141478841378911373 : Nat.Prime 141478841378911373 := by
  apply lucas_primality 141478841378911373 (2 : ZMod 141478841378911373)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (995369, 1), (267174959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (995369, 1), (267174959, 1)] : List FactorBlock).map factorBlockValue).prod) = 141478841378911373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_995369
      · exact prime_sixtyEightBN_267174959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141478841378911373) ^ 70739420689455686 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 141478841378911373) ^ 20211263054130196 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 141478841378911373) ^ 7446254809416388 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 141478841378911373) ^ 142137078188 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 141478841378911373) ^ 529536308 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_235538131061916299 : Nat.Prime 235538131061916299 := by
  apply lucas_primality 235538131061916299 (2 : ZMod 235538131061916299)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (43, 1), (35569032174859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (43, 1), (35569032174859, 1)] : List FactorBlock).map factorBlockValue).prod) = 235538131061916299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_43
      · exact prime_sixtyEightBN_35569032174859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 235538131061916299) ^ 117769065530958149 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 235538131061916299) ^ 33648304437416614 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 235538131061916299) ^ 21412557369265118 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 235538131061916299) ^ 5477630954928286 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 235538131061916299) ^ 6622 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_304749689015967463 : Nat.Prime 304749689015967463 := by
  apply lucas_primality 304749689015967463 (6 : ZMod 304749689015967463)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (47, 1), (40024913188333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (47, 1), (40024913188333, 1)] : List FactorBlock).map factorBlockValue).prod) = 304749689015967463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_40024913188333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 304749689015967463) ^ 152374844507983731 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 304749689015967463) ^ 101583229671989154 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 304749689015967463) ^ 6484035936509946 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 304749689015967463) ^ 7614 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_363985782955029121 : Nat.Prime 363985782955029121 := by
  apply lucas_primality 363985782955029121 (19 : ZMod 363985782955029121)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (17, 1), (7307, 1), (32573, 1), (46853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (17, 1), (7307, 1), (32573, 1), (46853, 1)] : List FactorBlock).map factorBlockValue).prod) = 363985782955029121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_7307
      · exact prime_sixtyEightBN_32573
      · exact prime_sixtyEightBN_46853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 363985782955029121) ^ 181992891477514560 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 363985782955029121) ^ 121328594318343040 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 363985782955029121) ^ 72797156591005824 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 363985782955029121) ^ 21410928409119360 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 363985782955029121) ^ 49813299980160 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 363985782955029121) ^ 11174462989440 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 363985782955029121) ^ 7768676135040 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_365841963558622403 : Nat.Prime 365841963558622403 := by
  apply lucas_primality 365841963558622403 (2 : ZMod 365841963558622403)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (30781, 1), (123829, 1), (578203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (30781, 1), (123829, 1), (578203, 1)] : List FactorBlock).map factorBlockValue).prod) = 365841963558622403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_83
      · exact prime_sixtyEightBN_30781
      · exact prime_sixtyEightBN_123829
      · exact prime_sixtyEightBN_578203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 365841963558622403) ^ 182920981779311201 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 365841963558622403) ^ 4407734500706294 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 365841963558622403) ^ 11885317681642 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 365841963558622403) ^ 2954412646138 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 365841963558622403) ^ 632722354534 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_397033373137745411 : Nat.Prime 397033373137745411 := by
  apply lucas_primality 397033373137745411 (2 : ZMod 397033373137745411)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (79, 1), (947, 1), (48245549587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (79, 1), (947, 1), (48245549587, 1)] : List FactorBlock).map factorBlockValue).prod) = 397033373137745411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_79
      · exact prime_sixtyEightBN_947
      · exact prime_sixtyEightBN_48245549587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 397033373137745411) ^ 198516686568872705 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397033373137745411) ^ 79406674627549082 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397033373137745411) ^ 36093943012522310 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397033373137745411) ^ 5025738900477790 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397033373137745411) ^ 419253825911030 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 397033373137745411) ^ 8229430 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_536720701146006323 : Nat.Prime 536720701146006323 := by
  apply lucas_primality 536720701146006323 (2 : ZMod 536720701146006323)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (241, 1), (563, 1), (7817581039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (241, 1), (563, 1), (7817581039, 1)] : List FactorBlock).map factorBlockValue).prod) = 536720701146006323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_241
      · exact prime_sixtyEightBN_563
      · exact prime_sixtyEightBN_7817581039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 536720701146006323) ^ 268360350573003161 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 536720701146006323) ^ 48792791013273302 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 536720701146006323) ^ 23335682658522014 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 536720701146006323) ^ 2227056851228242 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 536720701146006323) ^ 953322737381894 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 536720701146006323) ^ 68655598 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_688311028255042727 : Nat.Prime 688311028255042727 := by
  apply lucas_primality 688311028255042727 (5 : ZMod 688311028255042727)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1741, 1), (99191, 1), (1992891673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1741, 1), (99191, 1), (1992891673, 1)] : List FactorBlock).map factorBlockValue).prod) = 688311028255042727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_1741
      · exact prime_sixtyEightBN_99191
      · exact prime_sixtyEightBN_1992891673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 688311028255042727) ^ 344155514127521363 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 688311028255042727) ^ 395353835873086 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 688311028255042727) ^ 6939248805386 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 688311028255042727) ^ 345383062 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_749172311228018501 : Nat.Prime 749172311228018501 := by
  apply lucas_primality 749172311228018501 (3 : ZMod 749172311228018501)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (468581, 1), (3197621377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (468581, 1), (3197621377, 1)] : List FactorBlock).map factorBlockValue).prod) = 749172311228018501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_468581
      · exact prime_sixtyEightBN_3197621377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 749172311228018501) ^ 374586155614009250 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 749172311228018501) ^ 149834462245603700 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 749172311228018501) ^ 1598810688500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 749172311228018501) ^ 234290500 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_750351752762226721 : Nat.Prime 750351752762226721 := by
  apply lucas_primality 750351752762226721 (11 : ZMod 750351752762226721)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (983, 1), (366997, 1), (619027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (983, 1), (366997, 1), (619027, 1)] : List FactorBlock).map factorBlockValue).prod) = 750351752762226721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_983
      · exact prime_sixtyEightBN_366997
      · exact prime_sixtyEightBN_619027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 750351752762226721) ^ 375175876381113360 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 750351752762226721) ^ 250117250920742240 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 750351752762226721) ^ 150070350552445344 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 750351752762226721) ^ 107193107537460960 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 750351752762226721) ^ 763328334447840 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 750351752762226721) ^ 2044571897760 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 750351752762226721) ^ 1212147051360 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_782175236348177167 : Nat.Prime 782175236348177167 := by
  apply lucas_primality 782175236348177167 (6 : ZMod 782175236348177167)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (15259, 1), (776665570789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (15259, 1), (776665570789, 1)] : List FactorBlock).map factorBlockValue).prod) = 782175236348177167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_15259
      · exact prime_sixtyEightBN_776665570789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 782175236348177167) ^ 391087618174088583 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 782175236348177167) ^ 260725078782725722 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 782175236348177167) ^ 71106839668016106 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 782175236348177167) ^ 51259927672074 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 782175236348177167) ^ 1007094 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_949418596013481131 : Nat.Prime 949418596013481131 := by
  apply lucas_primality 949418596013481131 (2 : ZMod 949418596013481131)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10667, 1), (8900521196339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10667, 1), (8900521196339, 1)] : List FactorBlock).map factorBlockValue).prod) = 949418596013481131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_10667
      · exact prime_sixtyEightBN_8900521196339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 949418596013481131) ^ 474709298006740565 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 949418596013481131) ^ 189883719202696226 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 949418596013481131) ^ 89005211963390 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 949418596013481131) ^ 106670 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1196336560959319999 : Nat.Prime 1196336560959319999 := by
  apply lucas_primality 1196336560959319999 (7 : ZMod 1196336560959319999)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (61, 1), (79, 2), (211, 1), (313, 1), (344797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (61, 1), (79, 2), (211, 1), (313, 1), (344797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1196336560959319999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_61
      · exact prime_sixtyEightBN_79
      · exact prime_sixtyEightBN_211
      · exact prime_sixtyEightBN_313
      · exact prime_sixtyEightBN_344797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1196336560959319999) ^ 598168280479659999 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1196336560959319999) ^ 398778853653106666 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1196336560959319999) ^ 52014633085187826 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1196336560959319999) ^ 19612074769824918 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1196336560959319999) ^ 15143500771636962 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1196336560959319999) ^ 5669841521134218 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1196336560959319999) ^ 3822161536611246 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 1196336560959319999) ^ 3469683787734 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1342253015688123857 : Nat.Prime 1342253015688123857 := by
  apply lucas_primality 1342253015688123857 (3 : ZMod 1342253015688123857)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (83890813480507741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (83890813480507741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1342253015688123857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_83890813480507741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1342253015688123857) ^ 671126507844061928 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1342253015688123857) ^ 16 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1574203625849840581 : Nat.Prime 1574203625849840581 := by
  apply lucas_primality 1574203625849840581 (6 : ZMod 1574203625849840581)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 2), (17, 1), (137, 1), (25544745487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 2), (17, 1), (137, 1), (25544745487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1574203625849840581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_137
      · exact prime_sixtyEightBN_25544745487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1574203625849840581) ^ 787101812924920290 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1574203625849840581) ^ 524734541949946860 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1574203625849840581) ^ 314840725169968116 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1574203625849840581) ^ 224886232264262940 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1574203625849840581) ^ 92600213285284740 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1574203625849840581) ^ 11490537414962340 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1574203625849840581) ^ 61625340 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1674251575501221917 : Nat.Prime 1674251575501221917 := by
  apply lucas_primality 1674251575501221917 (2 : ZMod 1674251575501221917)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (2531, 1), (7190196242683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (2531, 1), (7190196242683, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674251575501221917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_2531
      · exact prime_sixtyEightBN_7190196242683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1674251575501221917) ^ 837125787750610958 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674251575501221917) ^ 72793546760922692 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674251575501221917) ^ 661498054326836 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674251575501221917) ^ 232852 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_2085871069168482851 : Nat.Prime 2085871069168482851 := by
  apply lucas_primality 2085871069168482851 (6 : ZMod 2085871069168482851)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (1511, 1), (952039557803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (1511, 1), (952039557803, 1)] : List FactorBlock).map factorBlockValue).prod) = 2085871069168482851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_29
      · exact prime_sixtyEightBN_1511
      · exact prime_sixtyEightBN_952039557803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2085871069168482851) ^ 1042935534584241425 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2085871069168482851) ^ 417174213833696570 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2085871069168482851) ^ 71926588592016650 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2085871069168482851) ^ 1380457358814350 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 2085871069168482851) ^ 2190950 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3223722381073514713 : Nat.Prime 3223722381073514713 := by
  apply lucas_primality 3223722381073514713 (5 : ZMod 3223722381073514713)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (224449, 1), (4071096371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (224449, 1), (4071096371, 1)] : List FactorBlock).map factorBlockValue).prod) = 3223722381073514713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_224449
      · exact prime_sixtyEightBN_4071096371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3223722381073514713) ^ 1611861190536757356 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3223722381073514713) ^ 1074574127024504904 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3223722381073514713) ^ 460531768724787816 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3223722381073514713) ^ 14362827996888 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 3223722381073514713) ^ 791856072 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3678016600188186241 : Nat.Prime 3678016600188186241 := by
  apply lucas_primality 3678016600188186241 (7 : ZMod 3678016600188186241)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (3560833, 1), (537973459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (3560833, 1), (537973459, 1)] : List FactorBlock).map factorBlockValue).prod) = 3678016600188186241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_3560833
      · exact prime_sixtyEightBN_537973459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3678016600188186241) ^ 1839008300094093120 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3678016600188186241) ^ 1226005533396062080 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3678016600188186241) ^ 735603320037637248 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3678016600188186241) ^ 1032909041280 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (7 : ZMod 3678016600188186241) ^ 6836799360 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4452067977473215349 : Nat.Prime 4452067977473215349 := by
  apply lucas_primality 4452067977473215349 (2 : ZMod 4452067977473215349)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82268581, 1), (13529065177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82268581, 1), (13529065177, 1)] : List FactorBlock).map factorBlockValue).prod) = 4452067977473215349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_82268581
      · exact prime_sixtyEightBN_13529065177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4452067977473215349) ^ 2226033988736607674 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4452067977473215349) ^ 54116260708 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4452067977473215349) ^ 329074324 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4785346243837279997 : Nat.Prime 4785346243837279997 := by
  apply lucas_primality 4785346243837279997 (2 : ZMod 4785346243837279997)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1196336560959319999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1196336560959319999, 1)] : List FactorBlock).map factorBlockValue).prod) = 4785346243837279997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_1196336560959319999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4785346243837279997) ^ 2392673121918639998 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 4785346243837279997) ^ 4 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_5122824429669828001 : Nat.Prime 5122824429669828001 := by
  apply lucas_primality 5122824429669828001 (19 : ZMod 5122824429669828001)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 3), (7, 1), (691, 1), (137447, 1), (642121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 3), (7, 1), (691, 1), (137447, 1), (642121, 1)] : List FactorBlock).map factorBlockValue).prod) = 5122824429669828001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_691
      · exact prime_sixtyEightBN_137447
      · exact prime_sixtyEightBN_642121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 5122824429669828001) ^ 2561412214834914000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 5122824429669828001) ^ 1707608143223276000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 5122824429669828001) ^ 1024564885933965600 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 5122824429669828001) ^ 731832061381404000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 5122824429669828001) ^ 7413638827308000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 5122824429669828001) ^ 37271271324000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 5122824429669828001) ^ 7977973668000 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_6683292295267688131 : Nat.Prime 6683292295267688131 := by
  apply lucas_primality 6683292295267688131 (3 : ZMod 6683292295267688131)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (787, 1), (1913123, 1), (147962471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (787, 1), (1913123, 1), (147962471, 1)] : List FactorBlock).map factorBlockValue).prod) = 6683292295267688131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_787
      · exact prime_sixtyEightBN_1913123
      · exact prime_sixtyEightBN_147962471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6683292295267688131) ^ 3341646147633844065 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6683292295267688131) ^ 2227764098422562710 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6683292295267688131) ^ 1336658459053537626 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6683292295267688131) ^ 8492112192207990 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6683292295267688131) ^ 3493393940310 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 6683292295267688131) ^ 45168834030 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_8792035321467984029 : Nat.Prime 8792035321467984029 := by
  apply lucas_primality 8792035321467984029 (2 : ZMod 8792035321467984029)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3023, 1), (727095213485609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3023, 1), (727095213485609, 1)] : List FactorBlock).map factorBlockValue).prod) = 8792035321467984029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3023
      · exact prime_sixtyEightBN_727095213485609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8792035321467984029) ^ 4396017660733992014 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8792035321467984029) ^ 2908380853942436 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8792035321467984029) ^ 12092 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_29738062321910616977 : Nat.Prime 29738062321910616977 := by
  apply lucas_primality 29738062321910616977 (3 : ZMod 29738062321910616977)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (546235933, 1), (3402611917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (546235933, 1), (3402611917, 1)] : List FactorBlock).map factorBlockValue).prod) = 29738062321910616977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_546235933
      · exact prime_sixtyEightBN_3402611917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29738062321910616977) ^ 14869031160955308488 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 29738062321910616977) ^ 54441790672 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 29738062321910616977) ^ 8739774928 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_32214072376514972569 : Nat.Prime 32214072376514972569 := by
  apply lucas_primality 32214072376514972569 (11 : ZMod 32214072376514972569)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1342253015688123857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1342253015688123857, 1)] : List FactorBlock).map factorBlockValue).prod) = 32214072376514972569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_1342253015688123857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 32214072376514972569) ^ 16107036188257486284 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 32214072376514972569) ^ 10738024125504990856 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 32214072376514972569) ^ 24 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_32313235533719774407 : Nat.Prime 32313235533719774407 := by
  apply lucas_primality 32313235533719774407 (3 : ZMod 32313235533719774407)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (461, 1), (77171, 1), (4883289241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (461, 1), (77171, 1), (4883289241, 1)] : List FactorBlock).map factorBlockValue).prod) = 32313235533719774407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_31
      · exact prime_sixtyEightBN_461
      · exact prime_sixtyEightBN_77171
      · exact prime_sixtyEightBN_4883289241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32313235533719774407) ^ 16156617766859887203 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313235533719774407) ^ 10771078511239924802 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313235533719774407) ^ 1042362436571605626 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313235533719774407) ^ 70093786407201246 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313235533719774407) ^ 418722519258786 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 32313235533719774407) ^ 6617104566 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_43427399618407273171 : Nat.Prime 43427399618407273171 := by
  apply lucas_primality 43427399618407273171 (10 : ZMod 43427399618407273171)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (67, 1), (79, 1), (821, 1), (25624427251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (67, 1), (79, 1), (821, 1), (25624427251, 1)] : List FactorBlock).map factorBlockValue).prod) = 43427399618407273171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_67
      · exact prime_sixtyEightBN_79
      · exact prime_sixtyEightBN_821
      · exact prime_sixtyEightBN_25624427251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 43427399618407273171) ^ 21713699809203636585 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 43427399618407273171) ^ 14475799872802424390 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 43427399618407273171) ^ 8685479923681454634 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 43427399618407273171) ^ 3340569201415944090 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 43427399618407273171) ^ 648170143558317510 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 43427399618407273171) ^ 549713919220345230 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 43427399618407273171) ^ 52895736441421770 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 43427399618407273171) ^ 1694765670 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_52188489457046064461 : Nat.Prime 52188489457046064461 := by
  apply lucas_primality 52188489457046064461 (3 : ZMod 52188489457046064461)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (277, 1), (1699, 1), (282713, 1), (1508629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (277, 1), (1699, 1), (282713, 1), (1508629, 1)] : List FactorBlock).map factorBlockValue).prod) = 52188489457046064461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_277
      · exact prime_sixtyEightBN_1699
      · exact prime_sixtyEightBN_282713
      · exact prime_sixtyEightBN_1508629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52188489457046064461) ^ 26094244728523032230 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52188489457046064461) ^ 10437697891409212892 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52188489457046064461) ^ 4014499189003543420 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52188489457046064461) ^ 188406099122909980 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52188489457046064461) ^ 30717180374953540 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52188489457046064461) ^ 184598831525420 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 52188489457046064461) ^ 34593322451740 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_58232895284711734459 : Nat.Prime 58232895284711734459 := by
  apply lucas_primality 58232895284711734459 (2 : ZMod 58232895284711734459)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18553, 1), (326323, 1), (1603080397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18553, 1), (326323, 1), (1603080397, 1)] : List FactorBlock).map factorBlockValue).prod) = 58232895284711734459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_18553
      · exact prime_sixtyEightBN_326323
      · exact prime_sixtyEightBN_1603080397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58232895284711734459) ^ 29116447642355867229 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58232895284711734459) ^ 19410965094903911486 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58232895284711734459) ^ 3138732026341386 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58232895284711734459) ^ 178451703633246 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 58232895284711734459) ^ 36325623714 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_86338703399834887109 : Nat.Prime 86338703399834887109 := by
  apply lucas_primality 86338703399834887109 (2 : ZMod 86338703399834887109)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (365841963558622403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (365841963558622403, 1)] : List FactorBlock).map factorBlockValue).prod) = 86338703399834887109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_59
      · exact prime_sixtyEightBN_365841963558622403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86338703399834887109) ^ 43169351699917443554 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 86338703399834887109) ^ 1463367854234489612 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 86338703399834887109) ^ 236 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_92800183313317028467 : Nat.Prime 92800183313317028467 := by
  apply lucas_primality 92800183313317028467 (3 : ZMod 92800183313317028467)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (86743, 1), (218651, 1), (47969231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (86743, 1), (218651, 1), (47969231, 1)] : List FactorBlock).map factorBlockValue).prod) = 92800183313317028467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_86743
      · exact prime_sixtyEightBN_218651
      · exact prime_sixtyEightBN_47969231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 92800183313317028467) ^ 46400091656658514233 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 92800183313317028467) ^ 30933394437772342822 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 92800183313317028467) ^ 5458834312548060498 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 92800183313317028467) ^ 1069829073392862 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 92800183313317028467) ^ 424421490472566 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 92800183313317028467) ^ 1934577256686 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_110071084095237560699 : Nat.Prime 110071084095237560699 := by
  apply lucas_primality 110071084095237560699 (2 : ZMod 110071084095237560699)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (53, 1), (79877419517588941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (53, 1), (79877419517588941, 1)] : List FactorBlock).map factorBlockValue).prod) = 110071084095237560699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_53
      · exact prime_sixtyEightBN_79877419517588941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110071084095237560699) ^ 55035542047618780349 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 110071084095237560699) ^ 8467006468864427746 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 110071084095237560699) ^ 2076812907457312466 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 110071084095237560699) ^ 1378 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_120071377472291180423 : Nat.Prime 120071377472291180423 := by
  apply lucas_primality 120071377472291180423 (5 : ZMod 120071377472291180423)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (304749689015967463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (304749689015967463, 1)] : List FactorBlock).map factorBlockValue).prod) = 120071377472291180423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_197
      · exact prime_sixtyEightBN_304749689015967463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 120071377472291180423) ^ 60035688736145590211 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 120071377472291180423) ^ 609499378031934926 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 120071377472291180423) ^ 394 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_129252942134879097629 : Nat.Prime 129252942134879097629 := by
  apply lucas_primality 129252942134879097629 (2 : ZMod 129252942134879097629)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (32313235533719774407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (32313235533719774407, 1)] : List FactorBlock).map factorBlockValue).prod) = 129252942134879097629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_32313235533719774407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 129252942134879097629) ^ 64626471067439548814 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 129252942134879097629) ^ 4 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_167191552117196161183 : Nat.Prime 167191552117196161183 := by
  apply lucas_primality 167191552117196161183 (3 : ZMod 167191552117196161183)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (359, 1), (12263, 1), (341203, 1), (687061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (359, 1), (12263, 1), (341203, 1), (687061, 1)] : List FactorBlock).map factorBlockValue).prod) = 167191552117196161183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_359
      · exact prime_sixtyEightBN_12263
      · exact prime_sixtyEightBN_341203
      · exact prime_sixtyEightBN_687061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 167191552117196161183) ^ 83595776058598080591 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 167191552117196161183) ^ 55730517372398720394 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 167191552117196161183) ^ 465714629852914098 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 167191552117196161183) ^ 13633821423566514 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 167191552117196161183) ^ 490006102282794 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 167191552117196161183) ^ 243343097799462 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_247757615329092712849 : Nat.Prime 247757615329092712849 := by
  apply lucas_primality 247757615329092712849 (13 : ZMod 247757615329092712849)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (101208176196524801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (101208176196524801, 1)] : List FactorBlock).map factorBlockValue).prod) = 247757615329092712849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_101208176196524801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 247757615329092712849) ^ 123878807664546356424 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 247757615329092712849) ^ 82585871776364237616 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 247757615329092712849) ^ 14573977372299571344 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 247757615329092712849) ^ 2448 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_371200733253268113869 : Nat.Prime 371200733253268113869 := by
  apply lucas_primality 371200733253268113869 (2 : ZMod 371200733253268113869)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (92800183313317028467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (92800183313317028467, 1)] : List FactorBlock).map factorBlockValue).prod) = 371200733253268113869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_92800183313317028467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 371200733253268113869) ^ 185600366626634056934 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 371200733253268113869) ^ 4 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_749586400228031805539 : Nat.Prime 749586400228031805539 := by
  apply lucas_primality 749586400228031805539 (2 : ZMod 749586400228031805539)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (397, 1), (17609, 1), (4873868612423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (397, 1), (17609, 1), (4873868612423, 1)] : List FactorBlock).map factorBlockValue).prod) = 749586400228031805539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_397
      · exact prime_sixtyEightBN_17609
      · exact prime_sixtyEightBN_4873868612423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 749586400228031805539) ^ 374793200114015902769 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 749586400228031805539) ^ 68144218202548345958 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 749586400228031805539) ^ 1888126952715445354 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 749586400228031805539) ^ 42568368460902482 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 749586400228031805539) ^ 153797006 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_839004835680755015201 : Nat.Prime 839004835680755015201 := by
  apply lucas_primality 839004835680755015201 (3 : ZMod 839004835680755015201)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (181, 1), (1559651, 1), (3715082599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (181, 1), (1559651, 1), (3715082599, 1)] : List FactorBlock).map factorBlockValue).prod) = 839004835680755015201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_181
      · exact prime_sixtyEightBN_1559651
      · exact prime_sixtyEightBN_3715082599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 839004835680755015201) ^ 419502417840377507600 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 839004835680755015201) ^ 167800967136151003040 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 839004835680755015201) ^ 4635385832490359200 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 839004835680755015201) ^ 537943960335200 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 839004835680755015201) ^ 225837464800 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1380179179508078591179 : Nat.Prime 1380179179508078591179 := by
  apply lucas_primality 1380179179508078591179 (3 : ZMod 1380179179508078591179)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (4289, 1), (2822764026105293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (4289, 1), (2822764026105293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1380179179508078591179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_4289
      · exact prime_sixtyEightBN_2822764026105293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1380179179508078591179) ^ 690089589754039295589 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380179179508078591179) ^ 460059726502692863726 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380179179508078591179) ^ 72641009447793610062 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380179179508078591179) ^ 321795098976003402 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380179179508078591179) ^ 488946 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1412289756742293332551 : Nat.Prime 1412289756742293332551 := by
  apply lucas_primality 1412289756742293332551 (6 : ZMod 1412289756742293332551)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (23, 1), (45484372197819431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (23, 1), (45484372197819431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1412289756742293332551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_45484372197819431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1412289756742293332551) ^ 706144878371146666275 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1412289756742293332551) ^ 470763252247431110850 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1412289756742293332551) ^ 282457951348458666510 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1412289756742293332551) ^ 61403902467056231850 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 1412289756742293332551) ^ 31050 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_1441893792720749380757 : Nat.Prime 1441893792720749380757 := by
  apply lucas_primality 1441893792720749380757 (2 : ZMod 1441893792720749380757)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (8792035321467984029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (8792035321467984029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441893792720749380757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_41
      · exact prime_sixtyEightBN_8792035321467984029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1441893792720749380757) ^ 720946896360374690378 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1441893792720749380757) ^ 35168141285871936116 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 1441893792720749380757) ^ 164 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3820110817839387496189 : Nat.Prime 3820110817839387496189 := by
  apply lucas_primality 3820110817839387496189 (10 : ZMod 3820110817839387496189)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4421, 1), (18919, 1), (3806063444551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4421, 1), (18919, 1), (3806063444551, 1)] : List FactorBlock).map factorBlockValue).prod) = 3820110817839387496189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_4421
      · exact prime_sixtyEightBN_18919
      · exact prime_sixtyEightBN_3806063444551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3820110817839387496189) ^ 1910055408919693748094 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3820110817839387496189) ^ 1273370272613129165396 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3820110817839387496189) ^ 864082971689524428 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3820110817839387496189) ^ 201919277860319652 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 3820110817839387496189) ^ 1003690788 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4266732667086820976401 : Nat.Prime 4266732667086820976401 := by
  apply lucas_primality 4266732667086820976401 (14 : ZMod 4266732667086820976401)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (2591, 1), (3907, 1), (229639, 1), (509843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (2591, 1), (3907, 1), (229639, 1), (509843, 1)] : List FactorBlock).map factorBlockValue).prod) = 4266732667086820976401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_2591
      · exact prime_sixtyEightBN_3907
      · exact prime_sixtyEightBN_229639
      · exact prime_sixtyEightBN_509843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4266732667086820976401) ^ 2133366333543410488200 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (14 : ZMod 4266732667086820976401) ^ 1422244222362273658800 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (14 : ZMod 4266732667086820976401) ^ 853346533417364195280 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (14 : ZMod 4266732667086820976401) ^ 1646751318829340400 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (14 : ZMod 4266732667086820976401) ^ 1092073884588385200 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (14 : ZMod 4266732667086820976401) ^ 18580174391487600 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (14 : ZMod 4266732667086820976401) ^ 8368718737114800 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_8423758921189152236867 : Nat.Prime 8423758921189152236867 := by
  apply lucas_primality 8423758921189152236867 (2 : ZMod 8423758921189152236867)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (247757615329092712849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (247757615329092712849, 1)] : List FactorBlock).map factorBlockValue).prod) = 8423758921189152236867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_247757615329092712849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8423758921189152236867) ^ 4211879460594576118433 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8423758921189152236867) ^ 495515230658185425698 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8423758921189152236867) ^ 34 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_21220462903453569570907 : Nat.Prime 21220462903453569570907 := by
  apply lucas_primality 21220462903453569570907 (3 : ZMod 21220462903453569570907)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (13, 2), (89123, 1), (1242411026657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (13, 2), (89123, 1), (1242411026657, 1)] : List FactorBlock).map factorBlockValue).prod) = 21220462903453569570907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_89123
      · exact prime_sixtyEightBN_1242411026657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21220462903453569570907) ^ 10610231451726784785453 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 21220462903453569570907) ^ 7073487634484523190302 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 21220462903453569570907) ^ 3031494700493367081558 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 21220462903453569570907) ^ 1632343300265659197762 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 21220462903453569570907) ^ 238103103614707422 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 21220462903453569570907) ^ 17080066458 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_23894799387663654848017 : Nat.Prime 23894799387663654848017 := by
  apply lucas_primality 23894799387663654848017 (5 : ZMod 23894799387663654848017)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (9283, 1), (131581883, 1), (135849001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (9283, 1), (131581883, 1), (135849001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23894799387663654848017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_9283
      · exact prime_sixtyEightBN_131581883
      · exact prime_sixtyEightBN_135849001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23894799387663654848017) ^ 11947399693831827424008 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23894799387663654848017) ^ 7964933129221218282672 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23894799387663654848017) ^ 2574038499155839152 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23894799387663654848017) ^ 181596423784752 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 23894799387663654848017) ^ 175892345264016 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_24299553121357270354253 : Nat.Prime 24299553121357270354253 := by
  apply lucas_primality 24299553121357270354253 (2 : ZMod 24299553121357270354253)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (129252942134879097629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (129252942134879097629, 1)] : List FactorBlock).map factorBlockValue).prod) = 24299553121357270354253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_129252942134879097629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24299553121357270354253) ^ 12149776560678635177126 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 24299553121357270354253) ^ 517011768539516390516 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 24299553121357270354253) ^ 188 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_26409720837798319309793 : Nat.Prime 26409720837798319309793 := by
  apply lucas_primality 26409720837798319309793 (5 : ZMod 26409720837798319309793)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (19, 1), (49081, 1), (126429607184747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (19, 1), (49081, 1), (126429607184747, 1)] : List FactorBlock).map factorBlockValue).prod) = 26409720837798319309793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_49081
      · exact prime_sixtyEightBN_126429607184747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26409720837798319309793) ^ 13204860418899159654896 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 26409720837798319309793) ^ 3772817262542617044256 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 26409720837798319309793) ^ 1389985307252543121568 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 26409720837798319309793) ^ 538084408178283232 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 26409720837798319309793) ^ 208888736 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_30968768235053079244127 : Nat.Prime 30968768235053079244127 := by
  apply lucas_primality 30968768235053079244127 (5 : ZMod 30968768235053079244127)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (223, 1), (141637, 1), (1867819, 1), (5584441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (223, 1), (141637, 1), (1867819, 1), (5584441, 1)] : List FactorBlock).map factorBlockValue).prod) = 30968768235053079244127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_47
      · exact prime_sixtyEightBN_223
      · exact prime_sixtyEightBN_141637
      · exact prime_sixtyEightBN_1867819
      · exact prime_sixtyEightBN_5584441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30968768235053079244127) ^ 15484384117526539622063 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 30968768235053079244127) ^ 658909962447937856258 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 30968768235053079244127) ^ 138873400157188696162 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 30968768235053079244127) ^ 218648857537600198 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 30968768235053079244127) ^ 16580176256400154 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 30968768235053079244127) ^ 5545544887134286 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_116955825768221367218231 : Nat.Prime 116955825768221367218231 := by
  apply lucas_primality 116955825768221367218231 (13 : ZMod 116955825768221367218231)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (71, 1), (4452067977473215349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (71, 1), (4452067977473215349, 1)] : List FactorBlock).map factorBlockValue).prod) = 116955825768221367218231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_71
      · exact prime_sixtyEightBN_4452067977473215349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 116955825768221367218231) ^ 58477912884110683609115 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 116955825768221367218231) ^ 23391165153644273443646 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 116955825768221367218231) ^ 3160968264005982897790 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 116955825768221367218231) ^ 1647265151665089679130 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (13 : ZMod 116955825768221367218231) ^ 26270 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_186379291194773389848017 : Nat.Prime 186379291194773389848017 := by
  apply lucas_primality 186379291194773389848017 (3 : ZMod 186379291194773389848017)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (83, 1), (113, 1), (1066999, 1), (166287301183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (83, 1), (113, 1), (1066999, 1), (166287301183, 1)] : List FactorBlock).map factorBlockValue).prod) = 186379291194773389848017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_83
      · exact prime_sixtyEightBN_113
      · exact prime_sixtyEightBN_1066999
      · exact prime_sixtyEightBN_166287301183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 186379291194773389848017) ^ 93189645597386694924008 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 186379291194773389848017) ^ 26625613027824769978288 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 186379291194773389848017) ^ 2245533628852691443952 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 186379291194773389848017) ^ 1649374258360826458832 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 186379291194773389848017) ^ 174676162953079984 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 186379291194773389848017) ^ 1120826965552 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_226639870430906223439123 : Nat.Prime 226639870430906223439123 := by
  apply lucas_primality 226639870430906223439123 (2 : ZMod 226639870430906223439123)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (179, 1), (1082399, 1), (14996893149419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (179, 1), (1082399, 1), (14996893149419, 1)] : List FactorBlock).map factorBlockValue).prod) = 226639870430906223439123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_179
      · exact prime_sixtyEightBN_1082399
      · exact prime_sixtyEightBN_14996893149419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 226639870430906223439123) ^ 113319935215453111719561 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 226639870430906223439123) ^ 75546623476968741146374 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 226639870430906223439123) ^ 17433836186992786418394 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 226639870430906223439123) ^ 1266144527546962142118 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 226639870430906223439123) ^ 209386622152188078 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 226639870430906223439123) ^ 15112454838 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_254044461392833520480737 : Nat.Prime 254044461392833520480737 := by
  apply lucas_primality 254044461392833520480737 (5 : ZMod 254044461392833520480737)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (79, 1), (4785346243837279997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (79, 1), (4785346243837279997, 1)] : List FactorBlock).map factorBlockValue).prod) = 254044461392833520480737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_79
      · exact prime_sixtyEightBN_4785346243837279997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 254044461392833520480737) ^ 127022230696416760240368 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 254044461392833520480737) ^ 84681487130944506826912 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 254044461392833520480737) ^ 36292065913261931497248 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 254044461392833520480737) ^ 3215752675858652157984 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 254044461392833520480737) ^ 53088 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_349837897160153510777761 : Nat.Prime 349837897160153510777761 := by
  apply lucas_primality 349837897160153510777761 (38 : ZMod 349837897160153510777761)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 2), (13, 1), (31, 1), (13410857, 1), (2752123753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 2), (13, 1), (31, 1), (13410857, 1), (2752123753, 1)] : List FactorBlock).map factorBlockValue).prod) = 349837897160153510777761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_7
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_31
      · exact prime_sixtyEightBN_13410857
      · exact prime_sixtyEightBN_2752123753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 349837897160153510777761) ^ 174918948580076755388880 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (38 : ZMod 349837897160153510777761) ^ 116612632386717836925920 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (38 : ZMod 349837897160153510777761) ^ 69967579432030702155552 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (38 : ZMod 349837897160153510777761) ^ 49976842451450501539680 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (38 : ZMod 349837897160153510777761) ^ 26910607473857962367520 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (38 : ZMod 349837897160153510777761) ^ 11285093456779145508960 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (38 : ZMod 349837897160153510777761) ^ 26086170120235680 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (38 : ZMod 349837897160153510777761) ^ 127115612725920 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_377079709003629972471049 : Nat.Prime 377079709003629972471049 := by
  apply lucas_primality 377079709003629972471049 (11 : ZMod 377079709003629972471049)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (683, 1), (971, 1), (23690923368940739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (683, 1), (971, 1), (23690923368940739, 1)] : List FactorBlock).map factorBlockValue).prod) = 377079709003629972471049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_683
      · exact prime_sixtyEightBN_971
      · exact prime_sixtyEightBN_23690923368940739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 377079709003629972471049) ^ 188539854501814986235524 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 377079709003629972471049) ^ 125693236334543324157016 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 377079709003629972471049) ^ 552093278189794981656 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 377079709003629972471049) ^ 388341615863676593688 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (11 : ZMod 377079709003629972471049) ^ 15916632 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_912812645407694950674697 : Nat.Prime 912812645407694950674697 := by
  apply lucas_primality 912812645407694950674697 (5 : ZMod 912812645407694950674697)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (914122009, 1), (41606984462531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (914122009, 1), (41606984462531, 1)] : List FactorBlock).map factorBlockValue).prod) = 912812645407694950674697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_914122009
      · exact prime_sixtyEightBN_41606984462531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 912812645407694950674697) ^ 456406322703847475337348 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 912812645407694950674697) ^ 304270881802564983558232 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 912812645407694950674697) ^ 998567627100744 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (5 : ZMod 912812645407694950674697) ^ 21938928216 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3039131596378177045732907 : Nat.Prime 3039131596378177045732907 := by
  apply lucas_primality 3039131596378177045732907 (2 : ZMod 3039131596378177045732907)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (12433, 1), (1674251575501221917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (12433, 1), (1674251575501221917, 1)] : List FactorBlock).map factorBlockValue).prod) = 3039131596378177045732907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_73
      · exact prime_sixtyEightBN_12433
      · exact prime_sixtyEightBN_1674251575501221917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3039131596378177045732907) ^ 1519565798189088522866453 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039131596378177045732907) ^ 41631939676413384188122 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039131596378177045732907) ^ 244440730023178399882 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039131596378177045732907) ^ 1815218 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3732492136078365634002163 : Nat.Prime 3732492136078365634002163 := by
  apply lucas_primality 3732492136078365634002163 (2 : ZMod 3732492136078365634002163)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4679, 1), (76245313, 1), (1743738892501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4679, 1), (76245313, 1), (1743738892501, 1)] : List FactorBlock).map factorBlockValue).prod) = 3732492136078365634002163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_4679
      · exact prime_sixtyEightBN_76245313
      · exact prime_sixtyEightBN_1743738892501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3732492136078365634002163) ^ 1866246068039182817001081 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3732492136078365634002163) ^ 1244164045359455211334054 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3732492136078365634002163) ^ 797711505894072586878 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3732492136078365634002163) ^ 48953725668073074 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 3732492136078365634002163) ^ 2140510917162 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_40439712333496940337410759 : Nat.Prime 40439712333496940337410759 := by
  apply lucas_primality 40439712333496940337410759 (19 : ZMod 40439712333496940337410759)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29803, 1), (52188489457046064461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29803, 1), (52188489457046064461, 1)] : List FactorBlock).map factorBlockValue).prod) = 40439712333496940337410759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_29803
      · exact prime_sixtyEightBN_52188489457046064461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 40439712333496940337410759) ^ 20219856166748470168705379 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 40439712333496940337410759) ^ 3110747102576687718262366 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 40439712333496940337410759) ^ 1356900725883197675986 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (19 : ZMod 40439712333496940337410759) ^ 774878 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_66717135368458022730931609 : Nat.Prime 66717135368458022730931609 := by
  apply lucas_primality 66717135368458022730931609 (71 : ZMod 66717135368458022730931609)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (131, 1), (21220462903453569570907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (131, 1), (21220462903453569570907, 1)] : List FactorBlock).map factorBlockValue).prod) = 66717135368458022730931609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_131
      · exact prime_sixtyEightBN_21220462903453569570907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (71 : ZMod 66717135368458022730931609) ^ 33358567684229011365465804 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (71 : ZMod 66717135368458022730931609) ^ 22239045122819340910310536 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (71 : ZMod 66717135368458022730931609) ^ 509291109682885669701768 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (71 : ZMod 66717135368458022730931609) ^ 3144 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_76275282845343375133560331 : Nat.Prime 76275282845343375133560331 := by
  apply lucas_primality 76275282845343375133560331 (10 : ZMod 76275282845343375133560331)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (23, 1), (37, 1), (3559, 1), (2031301, 1), (1977354131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (23, 1), (37, 1), (3559, 1), (2031301, 1), (1977354131, 1)] : List FactorBlock).map factorBlockValue).prod) = 76275282845343375133560331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_23
      · exact prime_sixtyEightBN_37
      · exact prime_sixtyEightBN_3559
      · exact prime_sixtyEightBN_2031301
      · exact prime_sixtyEightBN_1977354131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 76275282845343375133560331) ^ 38137641422671687566780165 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 25425094281781125044520110 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 15255056569068675026712066 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 6934116622303943193960030 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 4014488570807546059661070 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 3316316645449711962328710 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 2061494130955226354961090 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 21431661378292603296870 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 37549965684722931330 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (10 : ZMod 76275282845343375133560331) ^ 38574417019964430 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_167139601078985275240691453 : Nat.Prime 167139601078985275240691453 := by
  apply lucas_primality 167139601078985275240691453 (2 : ZMod 167139601078985275240691453)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (743, 1), (7351, 1), (14140639, 1), (541022215169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (743, 1), (7351, 1), (14140639, 1), (541022215169, 1)] : List FactorBlock).map factorBlockValue).prod) = 167139601078985275240691453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_743
      · exact prime_sixtyEightBN_7351
      · exact prime_sixtyEightBN_14140639
      · exact prime_sixtyEightBN_541022215169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 167139601078985275240691453) ^ 83569800539492637620345726 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167139601078985275240691453) ^ 224952356768486238547364 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167139601078985275240691453) ^ 22736988311656274689252 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167139601078985275240691453) ^ 11819805390618152068 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 167139601078985275240691453) ^ 308932972422908 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_231017667008597463766587899 : Nat.Prime 231017667008597463766587899 := by
  apply lucas_primality 231017667008597463766587899 (2 : ZMod 231017667008597463766587899)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (179, 1), (154989102071, 1), (219132808019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (179, 1), (154989102071, 1), (219132808019, 1)] : List FactorBlock).map factorBlockValue).prod) = 231017667008597463766587899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_19
      · exact prime_sixtyEightBN_179
      · exact prime_sixtyEightBN_154989102071
      · exact prime_sixtyEightBN_219132808019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 231017667008597463766587899) ^ 115508833504298731883293949 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 231017667008597463766587899) ^ 12158824579399866514030942 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 231017667008597463766587899) ^ 1290601491668142255679262 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 231017667008597463766587899) ^ 1490541360145238 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 231017667008597463766587899) ^ 1054235872286942 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_245853663972452346760772443 : Nat.Prime 245853663972452346760772443 := by
  apply lucas_primality 245853663972452346760772443 (2 : ZMod 245853663972452346760772443)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (113, 1), (162821, 1), (131004933804314627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (113, 1), (162821, 1), (131004933804314627, 1)] : List FactorBlock).map factorBlockValue).prod) = 245853663972452346760772443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_113
      · exact prime_sixtyEightBN_162821
      · exact prime_sixtyEightBN_131004933804314627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 245853663972452346760772443) ^ 122926831986226173380386221 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 245853663972452346760772443) ^ 81951221324150782253590814 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 245853663972452346760772443) ^ 14461980233673667456516026 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 245853663972452346760772443) ^ 2175696141349135812042234 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 245853663972452346760772443) ^ 1509962867028530390802 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 245853663972452346760772443) ^ 1876674846 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_281098419996475235632071989 : Nat.Prime 281098419996475235632071989 := by
  apply lucas_primality 281098419996475235632071989 (2 : ZMod 281098419996475235632071989)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (173, 1), (23894799387663654848017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (173, 1), (23894799387663654848017, 1)] : List FactorBlock).map factorBlockValue).prod) = 281098419996475235632071989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_173
      · exact prime_sixtyEightBN_23894799387663654848017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 281098419996475235632071989) ^ 140549209998237617816035994 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 281098419996475235632071989) ^ 16535201176263249154827764 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 281098419996475235632071989) ^ 1624846358361128529665156 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 281098419996475235632071989) ^ 11764 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_638048794595173947545814197 : Nat.Prime 638048794595173947545814197 := by
  apply lucas_primality 638048794595173947545814197 (2 : ZMod 638048794595173947545814197)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (26907249203, 1), (5928223931229983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (26907249203, 1), (5928223931229983, 1)] : List FactorBlock).map factorBlockValue).prod) = 638048794595173947545814197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_26907249203
      · exact prime_sixtyEightBN_5928223931229983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 638048794595173947545814197) ^ 319024397297586973772907098 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 638048794595173947545814197) ^ 23712895724919932 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 638048794595173947545814197) ^ 107628996812 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_3092082619961227591952791877 : Nat.Prime 3092082619961227591952791877 := by
  apply lucas_primality 3092082619961227591952791877 (3 : ZMod 3092082619961227591952791877)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (709, 1), (6053, 1), (1859387, 1), (7451797536487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (709, 1), (6053, 1), (1859387, 1), (7451797536487, 1)] : List FactorBlock).map factorBlockValue).prod) = 3092082619961227591952791877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_13
      · exact prime_sixtyEightBN_709
      · exact prime_sixtyEightBN_6053
      · exact prime_sixtyEightBN_1859387
      · exact prime_sixtyEightBN_7451797536487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3092082619961227591952791877) ^ 1546041309980613795976395938 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092082619961227591952791877) ^ 237852509227786737842522452 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092082619961227591952791877) ^ 4361188462568727210088564 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092082619961227591952791877) ^ 510834729879601452495092 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092082619961227591952791877) ^ 1662958071644702039948 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (3 : ZMod 3092082619961227591952791877) ^ 414944529131548 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_4466341562166217632820699381 : Nat.Prime 4466341562166217632820699381 := by
  apply lucas_primality 4466341562166217632820699381 (6 : ZMod 4466341562166217632820699381)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 2), (307, 1), (839004835680755015201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 2), (307, 1), (839004835680755015201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4466341562166217632820699381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_17
      · exact prime_sixtyEightBN_307
      · exact prime_sixtyEightBN_839004835680755015201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4466341562166217632820699381) ^ 2233170781083108816410349690 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 4466341562166217632820699381) ^ 1488780520722072544273566460 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 4466341562166217632820699381) ^ 893268312433243526564139876 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 4466341562166217632820699381) ^ 262725974245071625460041140 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 4466341562166217632820699381) ^ 14548343850704291963585340 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (6 : ZMod 4466341562166217632820699381) ^ 5323380 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_6184165239922455183905583757 : Nat.Prime 6184165239922455183905583757 := by
  apply lucas_primality 6184165239922455183905583757 (2 : ZMod 6184165239922455183905583757)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (193, 1), (82889, 1), (32214072376514972569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (193, 1), (82889, 1), (32214072376514972569, 1)] : List FactorBlock).map factorBlockValue).prod) = 6184165239922455183905583757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_193
      · exact prime_sixtyEightBN_82889
      · exact prime_sixtyEightBN_32214072376514972569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6184165239922455183905583757) ^ 3092082619961227591952791878 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6184165239922455183905583757) ^ 2061388413307485061301861252 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6184165239922455183905583757) ^ 32042306942603394735262092 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6184165239922455183905583757) ^ 74607791624008676469804 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 6184165239922455183905583757) ^ 191970924 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_8039414811899191739077258883 : Nat.Prime 8039414811899191739077258883 := by
  apply lucas_primality 8039414811899191739077258883 (2 : ZMod 8039414811899191739077258883)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (289669, 1), (167191552117196161183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (289669, 1), (167191552117196161183, 1)] : List FactorBlock).map factorBlockValue).prod) = 8039414811899191739077258883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_83
      · exact prime_sixtyEightBN_289669
      · exact prime_sixtyEightBN_167191552117196161183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8039414811899191739077258883) ^ 4019707405949595869538629441 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8039414811899191739077258883) ^ 96860419420472189627436854 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8039414811899191739077258883) ^ 27753797651454562756378 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 8039414811899191739077258883) ^ 48085054 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_26798049372997305796924196269 : Nat.Prime 26798049372997305796924196269 := by
  apply lucas_primality 26798049372997305796924196269 (2 : ZMod 26798049372997305796924196269)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2976165209, 1), (750351752762226721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2976165209, 1), (750351752762226721, 1)] : List FactorBlock).map factorBlockValue).prod) = 26798049372997305796924196269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_2976165209
      · exact prime_sixtyEightBN_750351752762226721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26798049372997305796924196269) ^ 13399024686498652898462098134 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26798049372997305796924196269) ^ 8932683124332435265641398756 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26798049372997305796924196269) ^ 9004221033146720652 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 26798049372997305796924196269) ^ 35713982508 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem prime_sixtyEightBN_80394148118991917390772588811 : Nat.Prime 80394148118991917390772588811 := by
  apply lucas_primality 80394148118991917390772588811 (2 : ZMod 80394148118991917390772588811)
  · rw [← sixtyEightBNFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (151, 1), (257, 1), (50627, 1), (56179, 1), (2207212919647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (151, 1), (257, 1), (50627, 1), (56179, 1), (2207212919647, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyEightBN_2
      · exact prime_sixtyEightBN_3
      · exact prime_sixtyEightBN_5
      · exact prime_sixtyEightBN_11
      · exact prime_sixtyEightBN_151
      · exact prime_sixtyEightBN_257
      · exact prime_sixtyEightBN_50627
      · exact prime_sixtyEightBN_56179
      · exact prime_sixtyEightBN_2207212919647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80394148118991917390772588811) ^ 40197074059495958695386294405 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 26798049372997305796924196270 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 16078829623798383478154517762 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 7308558919908356126433871710 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 532411576946966340336242310 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 312817696961058044322072330 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 1587969820826671882410030 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 1431035584809126495501390 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide
    · change (2 : ZMod 80394148118991917390772588811) ^ 36423376921810230 ≠ 1
      rw [← sixtyEightBNFastPow_eq_pow]
      decide

private theorem phi_sixtyEightBN_80394148118991917390772588800 : Nat.totient 80394148118991917390772588800 = 32157650994867471398136053760 := by
  rw [← show ((([(2, 8), (5, 2), (3896609, 1), (3223722381073514713, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_5, prime_sixtyEightBN_3896609, prime_sixtyEightBN_3223722381073514713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588801 : Nat.totient 80394148118991917390772588801 = 44923126234671785338342809600 := by
  rw [← show ((([(3, 1), (7, 2), (47, 1), (1163, 1), (155153, 1), (91423121, 1), (705364031, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_7, prime_sixtyEightBN_47, prime_sixtyEightBN_1163, prime_sixtyEightBN_155153, prime_sixtyEightBN_91423121, prime_sixtyEightBN_705364031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588802 : Nat.totient 80394148118991917390772588802 = 37104991439534731103433502512 := by
  rw [← show ((([(2, 1), (13, 1), (3092082619961227591952791877, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_13, prime_sixtyEightBN_3092082619961227591952791877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588803 : Nat.totient 80394148118991917390772588803 = 80212652291758505201012889000 := by
  rw [← show ((([(443, 1), (4178851, 1), (43427399618407273171, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_443, prime_sixtyEightBN_4178851, prime_sixtyEightBN_43427399618407273171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588804 : Nat.totient 80394148118991917390772588804 = 26798049363993084728063493120 := by
  rw [← show ((([(2, 2), (3, 2), (2976165209, 1), (750351752762226721, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_2976165209, prime_sixtyEightBN_750351752762226721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588805 : Nat.totient 80394148118991917390772588805 = 63580437056884699337961738240 := by
  rw [← show ((([(5, 1), (89, 1), (6421, 1), (28027, 1), (979273, 1), (1025135711239, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_5, prime_sixtyEightBN_89, prime_sixtyEightBN_6421, prime_sixtyEightBN_28027, prime_sixtyEightBN_979273, prime_sixtyEightBN_1025135711239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588806 : Nat.totient 80394148118991917390772588806 = 37828914053363419566670731264 := by
  rw [← show ((([(2, 1), (17, 1), (10433, 1), (226639870430906223439123, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_17, prime_sixtyEightBN_10433, prime_sixtyEightBN_226639870430906223439123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588807 : Nat.totient 80394148118991917390772588807 = 53596098745994611593848392536 := by
  rw [← show ((([(3, 1), (26798049372997305796924196269, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_26798049372997305796924196269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588808 : Nat.totient 80394148118991917390772588808 = 31751156569534860127739904000 := by
  rw [← show ((([(2, 3), (7, 1), (19, 1), (41, 1), (347, 1), (14591, 1), (363985782955029121, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_7, prime_sixtyEightBN_19, prime_sixtyEightBN_41, prime_sixtyEightBN_347, prime_sixtyEightBN_14591, prime_sixtyEightBN_363985782955029121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588809 : Nat.totient 80394148118991917390772588809 = 76893161396537278645027249536 := by
  rw [← show ((([(23, 1), (13759, 1), (254044461392833520480737, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_23, prime_sixtyEightBN_13759, prime_sixtyEightBN_254044461392833520480737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588810 : Nat.totient 80394148118991917390772588810 = 19284364405020579503579136000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (151, 1), (257, 1), (50627, 1), (56179, 1), (2207212919647, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_5, prime_sixtyEightBN_11, prime_sixtyEightBN_151, prime_sixtyEightBN_257, prime_sixtyEightBN_50627, prime_sixtyEightBN_56179, prime_sixtyEightBN_2207212919647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588811 : Nat.totient 80394148118991917390772588811 = 80394148118991917390772588810 := by
  rw [← show ((([(80394148118991917390772588811, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_80394148118991917390772588811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588812 : Nat.totient 80394148118991917390772588812 = 38880727746816125542444617600 := by
  rw [← show ((([(2, 2), (31, 1), (1979, 1), (3922207, 1), (83526916242885721, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_31, prime_sixtyEightBN_1979, prime_sixtyEightBN_3922207, prime_sixtyEightBN_83526916242885721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588813 : Nat.totient 80394148118991917390772588813 = 53560054709000110599296695920 := by
  rw [← show ((([(3, 3), (1487, 1), (57535091, 1), (34803017560367107, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_1487, prime_sixtyEightBN_57535091, prime_sixtyEightBN_34803017560367107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588814 : Nat.totient 80394148118991917390772588814 = 40140176172820738155435856824 := by
  rw [← show ((([(2, 1), (719, 1), (40507, 1), (1380179179508078591179, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_719, prime_sixtyEightBN_40507, prime_sixtyEightBN_1380179179508078591179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588815 : Nat.totient 80394148118991917390772588815 = 50886738496979311429069208064 := by
  rw [← show ((([(5, 1), (7, 1), (13, 1), (475997, 1), (371200733253268113869, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_5, prime_sixtyEightBN_7, prime_sixtyEightBN_13, prime_sixtyEightBN_475997, prime_sixtyEightBN_371200733253268113869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588816 : Nat.totient 80394148118991917390772588816 = 26797626817463901023814224896 := by
  rw [← show ((([(2, 4), (3, 1), (63419, 1), (26409720837798319309793, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_63419, prime_sixtyEightBN_26409720837798319309793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588817 : Nat.totient 80394148118991917390772588817 = 80057979857496682146475776000 := by
  rw [← show ((([(269, 1), (2153, 1), (792821, 1), (31363141, 1), (5582560421, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_269, prime_sixtyEightBN_2153, prime_sixtyEightBN_792821, prime_sixtyEightBN_31363141, prime_sixtyEightBN_5582560421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588818 : Nat.totient 80394148118991917390772588818 = 40197074059354479569886636304 := by
  rw [← show ((([(2, 1), (284120746733, 1), (141478841378911373, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_284120746733, prime_sixtyEightBN_141478841378911373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588819 : Nat.totient 80394148118991917390772588819 = 51748208822906616429778636800 := by
  rw [← show ((([(3, 1), (37, 2), (131, 1), (40627, 1), (3678016600188186241, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_37, prime_sixtyEightBN_131, prime_sixtyEightBN_40627, prime_sixtyEightBN_3678016600188186241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588820 : Nat.totient 80394148118991917390772588820 = 31770107892256689316927529856 := by
  rw [← show ((([(2, 2), (5, 1), (83, 1), (289669, 1), (167191552117196161183, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_5, prime_sixtyEightBN_83, prime_sixtyEightBN_289669, prime_sixtyEightBN_167191552117196161183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588821 : Nat.totient 80394148118991917390772588821 = 72055009278773089304590008000 := by
  rw [← show ((([(11, 1), (71, 1), (70223, 1), (401827, 1), (3648000672787021, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_11, prime_sixtyEightBN_71, prime_sixtyEightBN_70223, prime_sixtyEightBN_401827, prime_sixtyEightBN_3648000672787021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588822 : Nat.totient 80394148118991917390772588822 = 22969756605426262111649311056 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (638048794595173947545814197, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_7, prime_sixtyEightBN_638048794595173947545814197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588823 : Nat.totient 80394148118991917390772588823 = 71677516663682168715177461760 := by
  rw [← show ((([(17, 1), (29, 1), (53, 1), (7749517, 1), (397033373137745411, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_17, prime_sixtyEightBN_29, prime_sixtyEightBN_53, prime_sixtyEightBN_7749517, prime_sixtyEightBN_397033373137745411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588824 : Nat.totient 80394148118991917390772588824 = 39506811819870720223044077184 := by
  rw [← show ((([(2, 3), (59, 1), (5479, 1), (22963, 1), (1706863, 1), (793147297067, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_59, prime_sixtyEightBN_5479, prime_sixtyEightBN_22963, prime_sixtyEightBN_1706863, prime_sixtyEightBN_793147297067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588825 : Nat.totient 80394148118991917390772588825 = 42875640246066287151907564480 := by
  rw [← show ((([(3, 1), (5, 2), (34613, 1), (30968768235053079244127, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_5, prime_sixtyEightBN_34613, prime_sixtyEightBN_30968768235053079244127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588826 : Nat.totient 80394148118991917390772588826 = 39688250337216096393357597888 := by
  rw [← show ((([(2, 1), (79, 1), (5407271923699, 1), (94099895372753, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_79, prime_sixtyEightBN_5407271923699, prime_sixtyEightBN_94099895372753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588827 : Nat.totient 80394148118991917390772588827 = 76162876449151164534467010432 := by
  rw [← show ((([(19, 1), (116143793, 1), (1320306943, 1), (27593063767, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_19, prime_sixtyEightBN_116143793, prime_sixtyEightBN_1320306943, prime_sixtyEightBN_27593063767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588828 : Nat.totient 80394148118991917390772588828 = 24608194847028385193930194944 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (193, 1), (82889, 1), (32214072376514972569, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_13, prime_sixtyEightBN_193, prime_sixtyEightBN_82889, prime_sixtyEightBN_32214072376514972569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588829 : Nat.totient 80394148118991917390772588829 = 68898963700643621197241664000 := by
  rw [← show ((([(7, 1), (6691, 1), (11243291, 1), (59344907, 1), (2572518241, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_7, prime_sixtyEightBN_6691, prime_sixtyEightBN_11243291, prime_sixtyEightBN_59344907, prime_sixtyEightBN_2572518241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588830 : Nat.totient 80394148118991917390772588830 = 32157659247596766956309035528 := by
  rw [← show ((([(2, 1), (5, 1), (8039414811899191739077258883, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_5, prime_sixtyEightBN_8039414811899191739077258883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588831 : Nat.totient 80394148118991917390772588831 = 53423764011381899304830883840 := by
  rw [← show ((([(3, 2), (311, 1), (4468075553, 1), (6428372446993073, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_311, prime_sixtyEightBN_4468075553, prime_sixtyEightBN_6428372446993073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588832 : Nat.totient 80394148118991917390772588832 = 34953977200762541004033054720 := by
  rw [← show ((([(2, 5), (11, 1), (23, 1), (144272533, 1), (68828813230418249, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_11, prime_sixtyEightBN_23, prime_sixtyEightBN_144272533, prime_sixtyEightBN_68828813230418249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588833 : Nat.totient 80394148118991917390772588833 = 79854589769215939267293338800 := by
  rw [← show ((([(149, 1), (258672767, 1), (2085871069168482851, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_149, prime_sixtyEightBN_258672767, prime_sixtyEightBN_2085871069168482851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588834 : Nat.totient 80394148118991917390772588834 = 26124960381143977126060277760 := by
  rw [← show ((([(2, 1), (3, 1), (61, 1), (197, 1), (457, 1), (617, 1), (145069, 1), (27258449232647, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_61, prime_sixtyEightBN_197, prime_sixtyEightBN_457, prime_sixtyEightBN_617, prime_sixtyEightBN_145069, prime_sixtyEightBN_27258449232647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588835 : Nat.totient 80394148118991917390772588835 = 64315117134432099576795540960 := by
  rw [← show ((([(5, 1), (322891, 1), (29571383, 1), (1683940945780339, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_5, prime_sixtyEightBN_322891, prime_sixtyEightBN_29571383, prime_sixtyEightBN_1683940945780339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588836 : Nat.totient 80394148118991917390772588836 = 33643186866212926380847386624 := by
  rw [← show ((([(2, 2), (7, 1), (43, 1), (4789, 1), (10949, 1), (435593, 1), (2923464105533, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_7, prime_sixtyEightBN_43, prime_sixtyEightBN_4789, prime_sixtyEightBN_10949, prime_sixtyEightBN_435593, prime_sixtyEightBN_2923464105533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588837 : Nat.totient 80394148118991917390772588837 = 53544110926271907962321582400 := by
  rw [← show ((([(3, 1), (1031, 1), (16511389, 1), (1574203625849840581, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_1031, prime_sixtyEightBN_16511389, prime_sixtyEightBN_1574203625849840581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588838 : Nat.totient 80394148118991917390772588838 = 40193458297712424547848328960 := by
  rw [← show ((([(2, 1), (12377, 1), (109211, 1), (29738062321910616977, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_12377, prime_sixtyEightBN_109211, prime_sixtyEightBN_29738062321910616977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588839 : Nat.totient 80394148118991917390772588839 = 80131345515896777675939301120 := by
  rw [← show ((([(487, 1), (821, 1), (75421289, 1), (2665989096022613, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_487, prime_sixtyEightBN_821, prime_sixtyEightBN_75421289, prime_sixtyEightBN_2665989096022613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588840 : Nat.totient 80394148118991917390772588840 = 20111630539213613210436403200 := by
  rw [← show ((([(2, 3), (3, 3), (5, 1), (17, 2), (307, 1), (839004835680755015201, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_5, prime_sixtyEightBN_17, prime_sixtyEightBN_307, prime_sixtyEightBN_839004835680755015201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588841 : Nat.totient 80394148118991917390772588841 = 74209982879069462206867005072 := by
  rw [← show ((([(13, 1), (6184165239922455183905583757, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_13, prime_sixtyEightBN_6184165239922455183905583757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588842 : Nat.totient 80394148118991917390772588842 = 40197070239385140855988275744 := by
  rw [← show ((([(2, 1), (10522489, 1), (3820110817839387496189, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_10522489, prime_sixtyEightBN_3820110817839387496189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588843 : Nat.totient 80394148118991917390772588843 = 40415994026737433586470160000 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (31, 1), (99745656301, 1), (112552921338863, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_7, prime_sixtyEightBN_11, prime_sixtyEightBN_31, prime_sixtyEightBN_99745656301, prime_sixtyEightBN_112552921338863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588844 : Nat.totient 80394148118991917390772588844 = 39596052552174814963869987840 := by
  rw [← show ((([(2, 2), (73, 1), (787, 1), (349837897160153510777761, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_73, prime_sixtyEightBN_787, prime_sixtyEightBN_349837897160153510777761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588845 : Nat.totient 80394148118991917390772588845 = 64048449953719701821694343680 := by
  rw [← show ((([(5, 1), (241, 1), (66717135368458022730931609, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_5, prime_sixtyEightBN_241, prime_sixtyEightBN_66717135368458022730931609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588846 : Nat.totient 80394148118991917390772588846 = 25387322466465758471813066016 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (83717, 1), (8423758921189152236867, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_19, prime_sixtyEightBN_83717, prime_sixtyEightBN_8423758921189152236867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588847 : Nat.totient 80394148118991917390772588847 = 80394116035625415592026232320 := by
  rw [← show ((([(3498613, 1), (17074111, 1), (33957757, 1), (39632497, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3498613, prime_sixtyEightBN_17074111, prime_sixtyEightBN_33957757, prime_sixtyEightBN_39632497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588848 : Nat.totient 80394148118991917390772588848 = 38075129451109738929808982016 := by
  rw [← show ((([(2, 4), (47, 1), (67, 1), (97, 1), (137, 1), (120071377472291180423, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_47, prime_sixtyEightBN_67, prime_sixtyEightBN_97, prime_sixtyEightBN_137, prime_sixtyEightBN_120071377472291180423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588849 : Nat.totient 80394148118991917390772588849 = 52288816950784366595905920000 := by
  rw [← show ((([(3, 2), (41, 1), (874001, 1), (1104941063, 1), (225604120967, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_41, prime_sixtyEightBN_874001, prime_sixtyEightBN_1104941063, prime_sixtyEightBN_225604120967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588850 : Nat.totient 80394148118991917390772588850 = 27563699059456990007421984000 := by
  rw [← show ((([(2, 1), (5, 2), (7, 2), (3174191, 1), (150656393, 1), (68617948871, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_5, prime_sixtyEightBN_7, prime_sixtyEightBN_3174191, prime_sixtyEightBN_150656393, prime_sixtyEightBN_68617948871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588851 : Nat.totient 80394148118991917390772588851 = 79900698899565644375386372320 := by
  rw [← show ((([(163, 1), (342061, 1), (1441893792720749380757, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_163, prime_sixtyEightBN_342061, prime_sixtyEightBN_1441893792720749380757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588852 : Nat.totient 80394148118991917390772588852 = 25873978704962915941857844576 := by
  rw [← show ((([(2, 2), (3, 1), (29, 1), (231017667008597463766587899, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_29, prime_sixtyEightBN_231017667008597463766587899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588853 : Nat.totient 80394148118991917390772588853 = 79973236347596026494568732320 := by
  rw [← show ((([(191, 1), (70190420227, 1), (5996712498589529, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_191, prime_sixtyEightBN_70190420227, prime_sixtyEightBN_5996712498589529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588854 : Nat.totient 80394148118991917390772588854 = 33731810399577028275848638560 := by
  rw [← show ((([(2, 1), (11, 1), (13, 1), (281098419996475235632071989, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_11, prime_sixtyEightBN_13, prime_sixtyEightBN_281098419996475235632071989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588855 : Nat.totient 80394148118991917390772588855 = 40857830079242683373496115200 := by
  rw [← show ((([(3, 1), (5, 1), (23, 1), (521, 1), (541, 1), (89963, 1), (9189807721517513, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_5, prime_sixtyEightBN_23, prime_sixtyEightBN_521, prime_sixtyEightBN_541, prime_sixtyEightBN_89963, prime_sixtyEightBN_9189807721517513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588856 : Nat.totient 80394148118991917390772588856 = 39102833531986621227139645440 := by
  rw [← show ((([(2, 3), (37, 1), (4993, 1), (1877727767, 1), (28969335407581, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_37, prime_sixtyEightBN_4993, prime_sixtyEightBN_1877727767, prime_sixtyEightBN_28969335407581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588857 : Nat.totient 80394148118991917390772588857 = 64497464111434158155557359360 := by
  rw [← show ((([(7, 1), (17, 1), (181, 1), (3732492136078365634002163, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_7, prime_sixtyEightBN_17, prime_sixtyEightBN_181, prime_sixtyEightBN_3732492136078365634002163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588858 : Nat.totient 80394148118991917390772588858 = 26798049372997305796924196280 := by
  rw [← show ((([(2, 1), (3, 2), (4466341562166217632820699381, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_4466341562166217632820699381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588859 : Nat.totient 80394148118991917390772588859 = 80394031163166149169404683240 := by
  rw [← show ((([(687389, 1), (116955825768221367218231, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_687389, prime_sixtyEightBN_116955825768221367218231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588860 : Nat.totient 80394148118991917390772588860 = 32157659247595317545853824640 := by
  rw [← show ((([(2, 2), (5, 1), (25884937613641, 1), (155291369287723, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_5, prime_sixtyEightBN_25884937613641, prime_sixtyEightBN_155291369287723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588861 : Nat.totient 80394148118991917390772588861 = 53104391418049706900326847472 := by
  rw [← show ((([(3, 1), (109, 1), (245853663972452346760772443, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_109, prime_sixtyEightBN_245853663972452346760772443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588862 : Nat.totient 80394148118991917390772588862 = 39934905908765624795891652480 := by
  rw [← show ((([(2, 1), (179, 1), (1063, 1), (24687655633, 1), (8557133267491, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_179, prime_sixtyEightBN_1063, prime_sixtyEightBN_24687655633, prime_sixtyEightBN_8557133267491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588863 : Nat.totient 80394148118991917390772588863 = 79209453927359270868986999808 := by
  rw [← show ((([(103, 1), (227, 1), (1483, 1), (35025481817, 1), (66196661393, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_103, prime_sixtyEightBN_227, prime_sixtyEightBN_1483, prime_sixtyEightBN_35025481817, prime_sixtyEightBN_66196661393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588864 : Nat.totient 80394148118991917390772588864 = 22935818230011214923658199040 := by
  rw [← show ((([(2, 6), (3, 1), (7, 1), (677, 1), (2815607, 1), (15511121, 1), (2023118299, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_7, prime_sixtyEightBN_677, prime_sixtyEightBN_2815607, prime_sixtyEightBN_15511121, prime_sixtyEightBN_2023118299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588865 : Nat.totient 80394148118991917390772588865 = 55305571051197926009242836480 := by
  rw [← show ((([(5, 1), (11, 1), (19, 1), (647, 1), (20564003459, 1), (5782241126089, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_5, prime_sixtyEightBN_11, prime_sixtyEightBN_19, prime_sixtyEightBN_647, prime_sixtyEightBN_20564003459, prime_sixtyEightBN_5782241126089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588866 : Nat.totient 80394148118991917390772588866 = 40193303053608611097719463936 := by
  rw [← show ((([(2, 1), (12097, 1), (96097, 1), (1346623, 1), (25677982800319, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_12097, prime_sixtyEightBN_96097, prime_sixtyEightBN_1346623, prime_sixtyEightBN_25677982800319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588867 : Nat.totient 80394148118991917390772588867 = 49473317588606234130380224320 := by
  rw [← show ((([(3, 4), (13, 1), (11423669, 1), (6683292295267688131, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_13, prime_sixtyEightBN_11423669, prime_sixtyEightBN_6683292295267688131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588868 : Nat.totient 80394148118991917390772588868 = 40146673733858953538213787648 := by
  rw [← show ((([(2, 2), (809, 1), (59669, 1), (1000393, 1), (416194676596189, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_809, prime_sixtyEightBN_59669, prime_sixtyEightBN_1000393, prime_sixtyEightBN_416194676596189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588869 : Nat.totient 80394148118991917390772588869 = 80384584261607525617874880000 := by
  rw [← show ((([(14891, 1), (19301, 1), (8938126339, 1), (31294950881, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_14891, prime_sixtyEightBN_19301, prime_sixtyEightBN_8938126339, prime_sixtyEightBN_31294950881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588870 : Nat.totient 80394148118991917390772588870 = 21419645980151395777744478208 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1193, 1), (26017, 1), (86338703399834887109, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_5, prime_sixtyEightBN_1193, prime_sixtyEightBN_26017, prime_sixtyEightBN_86338703399834887109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588871 : Nat.totient 80394148118991917390772588871 = 68891035026700517272673513208 := by
  rw [← show ((([(7, 1), (3779, 1), (3039131596378177045732907, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_7, prime_sixtyEightBN_3779, prime_sixtyEightBN_3039131596378177045732907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588872 : Nat.totient 80394148118991917390772588872 = 39941041740460413684828600384 := by
  rw [← show ((([(2, 3), (157, 1), (215760316183, 1), (296662893552139, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_157, prime_sixtyEightBN_215760316183, prime_sixtyEightBN_296662893552139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588873 : Nat.totient 80394148118991917390772588873 = 53102845221401341637224692480 := by
  rw [← show ((([(3, 1), (113, 1), (2803, 1), (62492080771, 1), (1353869037739, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_113, prime_sixtyEightBN_2803, prime_sixtyEightBN_62492080771, prime_sixtyEightBN_1353869037739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588874 : Nat.totient 80394148118991917390772588874 = 36612135765764820064108958400 := by
  rw [← show ((([(2, 1), (17, 1), (31, 1), (76275282845343375133560331, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_17, prime_sixtyEightBN_31, prime_sixtyEightBN_76275282845343375133560331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588875 : Nat.totient 80394148118991917390772588875 = 64315318494529604904054962400 := by
  rw [← show ((([(5, 3), (96872189779, 1), (6639193213441309, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_5, prime_sixtyEightBN_96872189779, prime_sixtyEightBN_6639193213441309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588876 : Nat.totient 80394148118991917390772588876 = 23902179251030361885040819200 := by
  rw [← show ((([(2, 2), (3, 2), (11, 1), (53, 1), (924281, 1), (148975583, 1), (27818535499, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_11, prime_sixtyEightBN_53, prime_sixtyEightBN_924281, prime_sixtyEightBN_148975583, prime_sixtyEightBN_27818535499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588877 : Nat.totient 80394148118991917390772588877 = 79642721484151325767044741744 := by
  rw [← show ((([(107, 1), (1002349, 1), (749586400228031805539, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_107, prime_sixtyEightBN_1002349, prime_sixtyEightBN_749586400228031805539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588878 : Nat.totient 80394148118991917390772588878 = 32922716457176721607582367712 := by
  rw [← show ((([(2, 1), (7, 1), (23, 1), (1447, 1), (2963, 1), (58232895284711734459, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_7, prime_sixtyEightBN_23, prime_sixtyEightBN_1447, prime_sixtyEightBN_2963, prime_sixtyEightBN_58232895284711734459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588879 : Nat.totient 80394148118991917390772588879 = 52349677839200492103751493088 := by
  rw [← show ((([(3, 1), (43, 1), (9144884603, 1), (68148530855203517, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_43, prime_sixtyEightBN_9144884603, prime_sixtyEightBN_68148530855203517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588880 : Nat.totient 80394148118991917390772588880 = 29683901396272991984425820160 := by
  rw [← show ((([(2, 4), (5, 1), (13, 1), (404837, 1), (3232157, 1), (4141723, 1), (14263871, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_5, prime_sixtyEightBN_13, prime_sixtyEightBN_404837, prime_sixtyEightBN_3232157, prime_sixtyEightBN_4141723, prime_sixtyEightBN_14263871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588881 : Nat.totient 80394148118991917390772588881 = 77596377360817332366954557568 := by
  rw [← show ((([(29, 1), (3037, 1), (912812645407694950674697, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_29, prime_sixtyEightBN_3037, prime_sixtyEightBN_912812645407694950674697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588882 : Nat.totient 80394148118991917390772588882 = 26798049372939721840863369072 := by
  rw [← show ((([(2, 1), (3, 1), (465381060373, 1), (28791512649353239, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_465381060373, prime_sixtyEightBN_28791512649353239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588883 : Nat.totient 80394148118991917390772588883 = 79029914503063877410691954016 := by
  rw [← show ((([(59, 1), (48757, 1), (8813047247, 1), (3171095722603, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_59, prime_sixtyEightBN_48757, prime_sixtyEightBN_8813047247, prime_sixtyEightBN_3171095722603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588884 : Nat.totient 80394148118991917390772588884 = 37943909806168817397194227200 := by
  rw [← show ((([(2, 2), (19, 1), (313, 1), (2393, 1), (1412289756742293332551, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_19, prime_sixtyEightBN_313, prime_sixtyEightBN_2393, prime_sixtyEightBN_1412289756742293332551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588885 : Nat.totient 80394148118991917390772588885 = 36751610563347417615292867200 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (6889289779, 1), (37045838689502101, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_5, prime_sixtyEightBN_7, prime_sixtyEightBN_6889289779, prime_sixtyEightBN_37045838689502101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588886 : Nat.totient 80394148118991917390772588886 = 40197049759942837338114285960 := by
  rw [← show ((([(2, 1), (1654231, 1), (24299553121357270354253, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_1654231, prime_sixtyEightBN_24299553121357270354253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588887 : Nat.totient 80394148118991917390772588887 = 73085546531756890396111824000 := by
  rw [← show ((([(11, 1), (1712917, 1), (4266732667086820976401, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_11, prime_sixtyEightBN_1712917, prime_sixtyEightBN_4266732667086820976401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588888 : Nat.totient 80394148118991917390772588888 = 26798049332014710354334464000 := by
  rw [← show ((([(2, 3), (3, 1), (653888537, 1), (5122824429669828001, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_653888537, prime_sixtyEightBN_5122824429669828001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588889 : Nat.totient 80394148118991917390772588889 = 80394148118455196539838903524 := by
  rw [← show ((([(149787679043, 1), (536720701146006323, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_149787679043, prime_sixtyEightBN_536720701146006323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588890 : Nat.totient 80394148118991917390772588890 = 31336868973200606654408640000 := by
  rw [← show ((([(2, 1), (5, 1), (41, 1), (863, 1), (303283, 1), (749172311228018501, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_5, prime_sixtyEightBN_41, prime_sixtyEightBN_863, prime_sixtyEightBN_303283, prime_sixtyEightBN_749172311228018501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588891 : Nat.totient 80394148118991917390772588891 = 49943562897006995436380160000 := by
  rw [← show ((([(3, 1), (17, 1), (101, 1), (162059, 1), (932221, 1), (2289211, 1), (45128929, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_17, prime_sixtyEightBN_101, prime_sixtyEightBN_162059, prime_sixtyEightBN_932221, prime_sixtyEightBN_2289211, prime_sixtyEightBN_45128929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588892 : Nat.totient 80394148118991917390772588892 = 33969358360137429883425036720 := by
  rw [← show ((([(2, 2), (7, 1), (71, 1), (40439712333496940337410759, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_7, prime_sixtyEightBN_71, prime_sixtyEightBN_40439712333496940337410759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588893 : Nat.totient 80394148118991917390772588893 = 72204307666121638903978707264 := by
  rw [← show ((([(13, 1), (37, 1), (167139601078985275240691453, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_13, prime_sixtyEightBN_37, prime_sixtyEightBN_167139601078985275240691453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588894 : Nat.totient 80394148118991917390772588894 = 26496946455683447052738690624 := by
  rw [← show ((([(2, 1), (3, 3), (89, 1), (21386347, 1), (782175236348177167, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_89, prime_sixtyEightBN_21386347, prime_sixtyEightBN_782175236348177167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588895 : Nat.totient 80394148118991917390772588895 = 61914527411408907766696060800 := by
  rw [← show ((([(5, 1), (47, 1), (61, 2), (133571, 1), (688311028255042727, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_5, prime_sixtyEightBN_47, prime_sixtyEightBN_61, prime_sixtyEightBN_133571, prime_sixtyEightBN_688311028255042727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588896 : Nat.totient 80394148118991917390772588896 = 40197072298358613171220131328 := by
  rw [← show ((([(2, 5), (22824497, 1), (110071084095237560699, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_22824497, prime_sixtyEightBN_110071084095237560699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588897 : Nat.totient 80394148118991917390772588897 = 53165590628941282723679448000 := by
  rw [← show ((([(3, 1), (127, 1), (6563, 1), (136501, 1), (235538131061916299, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_3, prime_sixtyEightBN_127, prime_sixtyEightBN_6563, prime_sixtyEightBN_136501, prime_sixtyEightBN_235538131061916299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588898 : Nat.totient 80394148118991917390772588898 = 36501315831551381335197446400 := by
  rw [← show ((([(2, 1), (11, 2), (881, 1), (377079709003629972471049, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_11, prime_sixtyEightBN_881, prime_sixtyEightBN_377079709003629972471049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588899 : Nat.totient 80394148118991917390772588899 = 68901441886048605852573946944 := by
  rw [← show ((([(7, 2), (8803, 1), (186379291194773389848017, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_7, prime_sixtyEightBN_8803, prime_sixtyEightBN_186379291194773389848017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588900 : Nat.totient 80394148118991917390772588900 = 21438439422444356933880268800 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (282257473, 1), (949418596013481131, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_2, prime_sixtyEightBN_3, prime_sixtyEightBN_5, prime_sixtyEightBN_282257473, prime_sixtyEightBN_949418596013481131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyEightBN_80394148118991917390772588901 : Nat.totient 80394148118991917390772588901 = 76896508003237225575662227200 := by
  rw [← show ((([(23, 1), (35977, 1), (732841, 1), (132575079676415891, 1)] : List FactorBlock).map factorBlockValue).prod) = 80394148118991917390772588901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyEightBN_23, prime_sixtyEightBN_35977, prime_sixtyEightBN_732841, prime_sixtyEightBN_132575079676415891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyEightBN : certifiedKill 1 80394148118991917390772588799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyEightBN_80394148118991917390772588800, phi_sixtyEightBN_80394148118991917390772588801, phi_sixtyEightBN_80394148118991917390772588802,
    phi_sixtyEightBN_80394148118991917390772588803, phi_sixtyEightBN_80394148118991917390772588804, phi_sixtyEightBN_80394148118991917390772588805,
    phi_sixtyEightBN_80394148118991917390772588806, phi_sixtyEightBN_80394148118991917390772588807, phi_sixtyEightBN_80394148118991917390772588808,
    phi_sixtyEightBN_80394148118991917390772588809, phi_sixtyEightBN_80394148118991917390772588810, phi_sixtyEightBN_80394148118991917390772588811,
    phi_sixtyEightBN_80394148118991917390772588812, phi_sixtyEightBN_80394148118991917390772588813, phi_sixtyEightBN_80394148118991917390772588814,
    phi_sixtyEightBN_80394148118991917390772588815, phi_sixtyEightBN_80394148118991917390772588816, phi_sixtyEightBN_80394148118991917390772588817,
    phi_sixtyEightBN_80394148118991917390772588818, phi_sixtyEightBN_80394148118991917390772588819, phi_sixtyEightBN_80394148118991917390772588820,
    phi_sixtyEightBN_80394148118991917390772588821, phi_sixtyEightBN_80394148118991917390772588822, phi_sixtyEightBN_80394148118991917390772588823,
    phi_sixtyEightBN_80394148118991917390772588824, phi_sixtyEightBN_80394148118991917390772588825, phi_sixtyEightBN_80394148118991917390772588826,
    phi_sixtyEightBN_80394148118991917390772588827, phi_sixtyEightBN_80394148118991917390772588828, phi_sixtyEightBN_80394148118991917390772588829,
    phi_sixtyEightBN_80394148118991917390772588830, phi_sixtyEightBN_80394148118991917390772588831, phi_sixtyEightBN_80394148118991917390772588832,
    phi_sixtyEightBN_80394148118991917390772588833, phi_sixtyEightBN_80394148118991917390772588834, phi_sixtyEightBN_80394148118991917390772588835,
    phi_sixtyEightBN_80394148118991917390772588836, phi_sixtyEightBN_80394148118991917390772588837, phi_sixtyEightBN_80394148118991917390772588838,
    phi_sixtyEightBN_80394148118991917390772588839, phi_sixtyEightBN_80394148118991917390772588840, phi_sixtyEightBN_80394148118991917390772588841,
    phi_sixtyEightBN_80394148118991917390772588842, phi_sixtyEightBN_80394148118991917390772588843, phi_sixtyEightBN_80394148118991917390772588844,
    phi_sixtyEightBN_80394148118991917390772588845, phi_sixtyEightBN_80394148118991917390772588846, phi_sixtyEightBN_80394148118991917390772588847,
    phi_sixtyEightBN_80394148118991917390772588848, phi_sixtyEightBN_80394148118991917390772588849, phi_sixtyEightBN_80394148118991917390772588850,
    phi_sixtyEightBN_80394148118991917390772588851, phi_sixtyEightBN_80394148118991917390772588852, phi_sixtyEightBN_80394148118991917390772588853,
    phi_sixtyEightBN_80394148118991917390772588854, phi_sixtyEightBN_80394148118991917390772588855, phi_sixtyEightBN_80394148118991917390772588856,
    phi_sixtyEightBN_80394148118991917390772588857, phi_sixtyEightBN_80394148118991917390772588858, phi_sixtyEightBN_80394148118991917390772588859,
    phi_sixtyEightBN_80394148118991917390772588860, phi_sixtyEightBN_80394148118991917390772588861, phi_sixtyEightBN_80394148118991917390772588862,
    phi_sixtyEightBN_80394148118991917390772588863, phi_sixtyEightBN_80394148118991917390772588864, phi_sixtyEightBN_80394148118991917390772588865,
    phi_sixtyEightBN_80394148118991917390772588866, phi_sixtyEightBN_80394148118991917390772588867, phi_sixtyEightBN_80394148118991917390772588868,
    phi_sixtyEightBN_80394148118991917390772588869, phi_sixtyEightBN_80394148118991917390772588870, phi_sixtyEightBN_80394148118991917390772588871,
    phi_sixtyEightBN_80394148118991917390772588872, phi_sixtyEightBN_80394148118991917390772588873, phi_sixtyEightBN_80394148118991917390772588874,
    phi_sixtyEightBN_80394148118991917390772588875, phi_sixtyEightBN_80394148118991917390772588876, phi_sixtyEightBN_80394148118991917390772588877,
    phi_sixtyEightBN_80394148118991917390772588878, phi_sixtyEightBN_80394148118991917390772588879, phi_sixtyEightBN_80394148118991917390772588880,
    phi_sixtyEightBN_80394148118991917390772588881, phi_sixtyEightBN_80394148118991917390772588882, phi_sixtyEightBN_80394148118991917390772588883,
    phi_sixtyEightBN_80394148118991917390772588884, phi_sixtyEightBN_80394148118991917390772588885, phi_sixtyEightBN_80394148118991917390772588886,
    phi_sixtyEightBN_80394148118991917390772588887, phi_sixtyEightBN_80394148118991917390772588888, phi_sixtyEightBN_80394148118991917390772588889,
    phi_sixtyEightBN_80394148118991917390772588890, phi_sixtyEightBN_80394148118991917390772588891, phi_sixtyEightBN_80394148118991917390772588892,
    phi_sixtyEightBN_80394148118991917390772588893, phi_sixtyEightBN_80394148118991917390772588894, phi_sixtyEightBN_80394148118991917390772588895,
    phi_sixtyEightBN_80394148118991917390772588896, phi_sixtyEightBN_80394148118991917390772588897, phi_sixtyEightBN_80394148118991917390772588898,
    phi_sixtyEightBN_80394148118991917390772588899, phi_sixtyEightBN_80394148118991917390772588900, phi_sixtyEightBN_80394148118991917390772588901]

end TotientTailPeriodKiller
end Erdos249257
