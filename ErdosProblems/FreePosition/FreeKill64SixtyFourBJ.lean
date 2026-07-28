import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyFourBJFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyFourBJFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : sixtyFourBJFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyFourBJFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyFourBJFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyFourBJFastPow a n * sixtyFourBJFastPow a n * a else sixtyFourBJFastPow a n * sixtyFourBJFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyFourBJ_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtyFourBJ_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtyFourBJ_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtyFourBJ_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtyFourBJ_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtyFourBJ_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtyFourBJ_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtyFourBJ_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtyFourBJ_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtyFourBJ_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtyFourBJ_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtyFourBJ_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtyFourBJ_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtyFourBJ_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtyFourBJ_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtyFourBJ_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtyFourBJ_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtyFourBJ_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtyFourBJ_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtyFourBJ_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtyFourBJ_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtyFourBJ_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtyFourBJ_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtyFourBJ_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtyFourBJ_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtyFourBJ_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtyFourBJ_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtyFourBJ_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtyFourBJ_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtyFourBJ_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtyFourBJ_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtyFourBJ_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtyFourBJ_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtyFourBJ_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtyFourBJ_151 : Nat.Prime 151 := by norm_num
private theorem prime_sixtyFourBJ_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixtyFourBJ_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtyFourBJ_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixtyFourBJ_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtyFourBJ_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtyFourBJ_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixtyFourBJ_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixtyFourBJ_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixtyFourBJ_199 : Nat.Prime 199 := by norm_num
private theorem prime_sixtyFourBJ_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtyFourBJ_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixtyFourBJ_229 : Nat.Prime 229 := by norm_num
private theorem prime_sixtyFourBJ_233 : Nat.Prime 233 := by norm_num
private theorem prime_sixtyFourBJ_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixtyFourBJ_241 : Nat.Prime 241 := by norm_num
private theorem prime_sixtyFourBJ_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtyFourBJ_257 : Nat.Prime 257 := by norm_num
private theorem prime_sixtyFourBJ_263 : Nat.Prime 263 := by norm_num
private theorem prime_sixtyFourBJ_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixtyFourBJ_271 : Nat.Prime 271 := by norm_num
private theorem prime_sixtyFourBJ_281 : Nat.Prime 281 := by norm_num
private theorem prime_sixtyFourBJ_283 : Nat.Prime 283 := by norm_num
private theorem prime_sixtyFourBJ_311 : Nat.Prime 311 := by norm_num
private theorem prime_sixtyFourBJ_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtyFourBJ_317 : Nat.Prime 317 := by norm_num
private theorem prime_sixtyFourBJ_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtyFourBJ_337 : Nat.Prime 337 := by norm_num
private theorem prime_sixtyFourBJ_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtyFourBJ_349 : Nat.Prime 349 := by norm_num
private theorem prime_sixtyFourBJ_353 : Nat.Prime 353 := by norm_num
private theorem prime_sixtyFourBJ_359 : Nat.Prime 359 := by norm_num
private theorem prime_sixtyFourBJ_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtyFourBJ_401 : Nat.Prime 401 := by norm_num
private theorem prime_sixtyFourBJ_409 : Nat.Prime 409 := by norm_num
private theorem prime_sixtyFourBJ_419 : Nat.Prime 419 := by norm_num
private theorem prime_sixtyFourBJ_433 : Nat.Prime 433 := by norm_num
private theorem prime_sixtyFourBJ_457 : Nat.Prime 457 := by norm_num
private theorem prime_sixtyFourBJ_461 : Nat.Prime 461 := by norm_num
private theorem prime_sixtyFourBJ_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixtyFourBJ_491 : Nat.Prime 491 := by norm_num
private theorem prime_sixtyFourBJ_503 : Nat.Prime 503 := by norm_num
private theorem prime_sixtyFourBJ_521 : Nat.Prime 521 := by norm_num
private theorem prime_sixtyFourBJ_541 : Nat.Prime 541 := by norm_num
private theorem prime_sixtyFourBJ_563 : Nat.Prime 563 := by norm_num
private theorem prime_sixtyFourBJ_571 : Nat.Prime 571 := by norm_num
private theorem prime_sixtyFourBJ_577 : Nat.Prime 577 := by norm_num
private theorem prime_sixtyFourBJ_587 : Nat.Prime 587 := by norm_num
private theorem prime_sixtyFourBJ_593 : Nat.Prime 593 := by norm_num
private theorem prime_sixtyFourBJ_607 : Nat.Prime 607 := by norm_num
private theorem prime_sixtyFourBJ_613 : Nat.Prime 613 := by norm_num
private theorem prime_sixtyFourBJ_631 : Nat.Prime 631 := by norm_num
private theorem prime_sixtyFourBJ_643 : Nat.Prime 643 := by norm_num
private theorem prime_sixtyFourBJ_727 : Nat.Prime 727 := by norm_num
private theorem prime_sixtyFourBJ_733 : Nat.Prime 733 := by norm_num
private theorem prime_sixtyFourBJ_743 : Nat.Prime 743 := by norm_num
private theorem prime_sixtyFourBJ_751 : Nat.Prime 751 := by norm_num
private theorem prime_sixtyFourBJ_757 : Nat.Prime 757 := by norm_num
private theorem prime_sixtyFourBJ_773 : Nat.Prime 773 := by norm_num
private theorem prime_sixtyFourBJ_809 : Nat.Prime 809 := by norm_num
private theorem prime_sixtyFourBJ_823 : Nat.Prime 823 := by norm_num
private theorem prime_sixtyFourBJ_839 : Nat.Prime 839 := by norm_num
private theorem prime_sixtyFourBJ_859 : Nat.Prime 859 := by norm_num
private theorem prime_sixtyFourBJ_877 : Nat.Prime 877 := by norm_num
private theorem prime_sixtyFourBJ_941 : Nat.Prime 941 := by norm_num
private theorem prime_sixtyFourBJ_983 : Nat.Prime 983 := by norm_num
private theorem prime_sixtyFourBJ_997 : Nat.Prime 997 := by norm_num
private theorem prime_sixtyFourBJ_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_sixtyFourBJ_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_sixtyFourBJ_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_sixtyFourBJ_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_sixtyFourBJ_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_sixtyFourBJ_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_sixtyFourBJ_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_sixtyFourBJ_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_sixtyFourBJ_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_sixtyFourBJ_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_sixtyFourBJ_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_sixtyFourBJ_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_sixtyFourBJ_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_sixtyFourBJ_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_sixtyFourBJ_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_sixtyFourBJ_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_sixtyFourBJ_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_sixtyFourBJ_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_sixtyFourBJ_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_sixtyFourBJ_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_sixtyFourBJ_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_sixtyFourBJ_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_sixtyFourBJ_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_sixtyFourBJ_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_sixtyFourBJ_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_sixtyFourBJ_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_sixtyFourBJ_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_sixtyFourBJ_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_sixtyFourBJ_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_sixtyFourBJ_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_sixtyFourBJ_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_sixtyFourBJ_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_sixtyFourBJ_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_sixtyFourBJ_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_sixtyFourBJ_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_sixtyFourBJ_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_sixtyFourBJ_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_sixtyFourBJ_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_sixtyFourBJ_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_sixtyFourBJ_2693 : Nat.Prime 2693 := by norm_num
private theorem prime_sixtyFourBJ_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_sixtyFourBJ_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_sixtyFourBJ_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_sixtyFourBJ_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_sixtyFourBJ_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_sixtyFourBJ_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_sixtyFourBJ_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_sixtyFourBJ_3119 : Nat.Prime 3119 := by norm_num
private theorem prime_sixtyFourBJ_3541 : Nat.Prime 3541 := by norm_num
private theorem prime_sixtyFourBJ_3557 : Nat.Prime 3557 := by norm_num
private theorem prime_sixtyFourBJ_3739 : Nat.Prime 3739 := by norm_num
private theorem prime_sixtyFourBJ_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_sixtyFourBJ_3929 : Nat.Prime 3929 := by norm_num
private theorem prime_sixtyFourBJ_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_sixtyFourBJ_4129 : Nat.Prime 4129 := by norm_num
private theorem prime_sixtyFourBJ_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_sixtyFourBJ_4297 : Nat.Prime 4297 := by norm_num
private theorem prime_sixtyFourBJ_4547 : Nat.Prime 4547 := by norm_num
private theorem prime_sixtyFourBJ_4691 : Nat.Prime 4691 := by norm_num
private theorem prime_sixtyFourBJ_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_sixtyFourBJ_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_sixtyFourBJ_5099 : Nat.Prime 5099 := by norm_num
private theorem prime_sixtyFourBJ_5233 : Nat.Prime 5233 := by norm_num
private theorem prime_sixtyFourBJ_5501 : Nat.Prime 5501 := by norm_num
private theorem prime_sixtyFourBJ_5521 : Nat.Prime 5521 := by norm_num
private theorem prime_sixtyFourBJ_5693 : Nat.Prime 5693 := by norm_num
private theorem prime_sixtyFourBJ_5749 : Nat.Prime 5749 := by norm_num
private theorem prime_sixtyFourBJ_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_sixtyFourBJ_5903 : Nat.Prime 5903 := by norm_num
private theorem prime_sixtyFourBJ_6089 : Nat.Prime 6089 := by norm_num
private theorem prime_sixtyFourBJ_6197 : Nat.Prime 6197 := by norm_num
private theorem prime_sixtyFourBJ_6229 : Nat.Prime 6229 := by norm_num
private theorem prime_sixtyFourBJ_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_sixtyFourBJ_6353 : Nat.Prime 6353 := by norm_num
private theorem prime_sixtyFourBJ_6397 : Nat.Prime 6397 := by norm_num
private theorem prime_sixtyFourBJ_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_sixtyFourBJ_6553 : Nat.Prime 6553 := by norm_num
private theorem prime_sixtyFourBJ_6571 : Nat.Prime 6571 := by norm_num
private theorem prime_sixtyFourBJ_6761 : Nat.Prime 6761 := by norm_num
private theorem prime_sixtyFourBJ_7577 : Nat.Prime 7577 := by norm_num
private theorem prime_sixtyFourBJ_7639 : Nat.Prime 7639 := by norm_num
private theorem prime_sixtyFourBJ_7699 : Nat.Prime 7699 := by norm_num
private theorem prime_sixtyFourBJ_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_sixtyFourBJ_7937 : Nat.Prime 7937 := by norm_num
private theorem prime_sixtyFourBJ_7993 : Nat.Prime 7993 := by norm_num
private theorem prime_sixtyFourBJ_8017 : Nat.Prime 8017 := by norm_num
private theorem prime_sixtyFourBJ_8167 : Nat.Prime 8167 := by norm_num
private theorem prime_sixtyFourBJ_8513 : Nat.Prime 8513 := by norm_num
private theorem prime_sixtyFourBJ_8941 : Nat.Prime 8941 := by norm_num
private theorem prime_sixtyFourBJ_9613 : Nat.Prime 9613 := by norm_num
private theorem prime_sixtyFourBJ_9851 : Nat.Prime 9851 := by norm_num
private theorem prime_sixtyFourBJ_10007 : Nat.Prime 10007 := by norm_num
private theorem prime_sixtyFourBJ_10067 : Nat.Prime 10067 := by norm_num
private theorem prime_sixtyFourBJ_10369 : Nat.Prime 10369 := by norm_num
private theorem prime_sixtyFourBJ_10601 : Nat.Prime 10601 := by norm_num
private theorem prime_sixtyFourBJ_10987 : Nat.Prime 10987 := by norm_num
private theorem prime_sixtyFourBJ_11273 : Nat.Prime 11273 := by norm_num
private theorem prime_sixtyFourBJ_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_sixtyFourBJ_12101 : Nat.Prime 12101 := by norm_num
private theorem prime_sixtyFourBJ_12263 : Nat.Prime 12263 := by norm_num
private theorem prime_sixtyFourBJ_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_sixtyFourBJ_12601 : Nat.Prime 12601 := by norm_num
private theorem prime_sixtyFourBJ_12713 : Nat.Prime 12713 := by norm_num
private theorem prime_sixtyFourBJ_13217 : Nat.Prime 13217 := by norm_num
private theorem prime_sixtyFourBJ_13469 : Nat.Prime 13469 := by norm_num
private theorem prime_sixtyFourBJ_13523 : Nat.Prime 13523 := by norm_num
private theorem prime_sixtyFourBJ_13709 : Nat.Prime 13709 := by norm_num
private theorem prime_sixtyFourBJ_13859 : Nat.Prime 13859 := by norm_num
private theorem prime_sixtyFourBJ_13931 : Nat.Prime 13931 := by norm_num
private theorem prime_sixtyFourBJ_14221 : Nat.Prime 14221 := by norm_num
private theorem prime_sixtyFourBJ_14479 : Nat.Prime 14479 := by norm_num
private theorem prime_sixtyFourBJ_14489 : Nat.Prime 14489 := by norm_num
private theorem prime_sixtyFourBJ_15199 : Nat.Prime 15199 := by norm_num
private theorem prime_sixtyFourBJ_15241 : Nat.Prime 15241 := by norm_num
private theorem prime_sixtyFourBJ_15359 : Nat.Prime 15359 := by norm_num
private theorem prime_sixtyFourBJ_15773 : Nat.Prime 15773 := by norm_num
private theorem prime_sixtyFourBJ_15823 : Nat.Prime 15823 := by norm_num
private theorem prime_sixtyFourBJ_18133 : Nat.Prime 18133 := by norm_num
private theorem prime_sixtyFourBJ_18257 : Nat.Prime 18257 := by norm_num
private theorem prime_sixtyFourBJ_19429 : Nat.Prime 19429 := by norm_num
private theorem prime_sixtyFourBJ_19927 : Nat.Prime 19927 := by norm_num
private theorem prime_sixtyFourBJ_19973 : Nat.Prime 19973 := by norm_num
private theorem prime_sixtyFourBJ_20107 : Nat.Prime 20107 := by norm_num
private theorem prime_sixtyFourBJ_20543 : Nat.Prime 20543 := by norm_num
private theorem prime_sixtyFourBJ_21401 : Nat.Prime 21401 := by norm_num
private theorem prime_sixtyFourBJ_21487 : Nat.Prime 21487 := by norm_num
private theorem prime_sixtyFourBJ_22159 : Nat.Prime 22159 := by norm_num
private theorem prime_sixtyFourBJ_22343 : Nat.Prime 22343 := by norm_num
private theorem prime_sixtyFourBJ_22717 : Nat.Prime 22717 := by norm_num
private theorem prime_sixtyFourBJ_22807 : Nat.Prime 22807 := by norm_num
private theorem prime_sixtyFourBJ_23357 : Nat.Prime 23357 := by norm_num
private theorem prime_sixtyFourBJ_23627 : Nat.Prime 23627 := by norm_num
private theorem prime_sixtyFourBJ_23831 : Nat.Prime 23831 := by norm_num
private theorem prime_sixtyFourBJ_25997 : Nat.Prime 25997 := by norm_num
private theorem prime_sixtyFourBJ_27011 : Nat.Prime 27011 := by norm_num
private theorem prime_sixtyFourBJ_27751 : Nat.Prime 27751 := by norm_num
private theorem prime_sixtyFourBJ_28051 : Nat.Prime 28051 := by norm_num
private theorem prime_sixtyFourBJ_28123 : Nat.Prime 28123 := by norm_num
private theorem prime_sixtyFourBJ_30011 : Nat.Prime 30011 := by norm_num
private theorem prime_sixtyFourBJ_30871 : Nat.Prime 30871 := by norm_num
private theorem prime_sixtyFourBJ_31657 : Nat.Prime 31657 := by norm_num
private theorem prime_sixtyFourBJ_31751 : Nat.Prime 31751 := by norm_num
private theorem prime_sixtyFourBJ_32099 : Nat.Prime 32099 := by norm_num
private theorem prime_sixtyFourBJ_32507 : Nat.Prime 32507 := by norm_num
private theorem prime_sixtyFourBJ_32933 : Nat.Prime 32933 := by norm_num
private theorem prime_sixtyFourBJ_33547 : Nat.Prime 33547 := by norm_num
private theorem prime_sixtyFourBJ_34649 : Nat.Prime 34649 := by norm_num
private theorem prime_sixtyFourBJ_35797 : Nat.Prime 35797 := by norm_num
private theorem prime_sixtyFourBJ_37321 : Nat.Prime 37321 := by norm_num
private theorem prime_sixtyFourBJ_37633 : Nat.Prime 37633 := by norm_num
private theorem prime_sixtyFourBJ_39199 : Nat.Prime 39199 := by norm_num
private theorem prime_sixtyFourBJ_41381 : Nat.Prime 41381 := by norm_num
private theorem prime_sixtyFourBJ_41549 : Nat.Prime 41549 := by norm_num
private theorem prime_sixtyFourBJ_42139 : Nat.Prime 42139 := by norm_num
private theorem prime_sixtyFourBJ_44851 : Nat.Prime 44851 := by norm_num
private theorem prime_sixtyFourBJ_47527 : Nat.Prime 47527 := by norm_num
private theorem prime_sixtyFourBJ_47623 : Nat.Prime 47623 := by norm_num
private theorem prime_sixtyFourBJ_47939 : Nat.Prime 47939 := by norm_num
private theorem prime_sixtyFourBJ_48751 : Nat.Prime 48751 := by norm_num
private theorem prime_sixtyFourBJ_50929 : Nat.Prime 50929 := by norm_num
private theorem prime_sixtyFourBJ_53047 : Nat.Prime 53047 := by norm_num
private theorem prime_sixtyFourBJ_53411 : Nat.Prime 53411 := by norm_num
private theorem prime_sixtyFourBJ_56417 : Nat.Prime 56417 := by norm_num
private theorem prime_sixtyFourBJ_63439 : Nat.Prime 63439 := by norm_num
private theorem prime_sixtyFourBJ_68771 : Nat.Prime 68771 := by norm_num
private theorem prime_sixtyFourBJ_69911 : Nat.Prime 69911 := by norm_num
private theorem prime_sixtyFourBJ_70589 : Nat.Prime 70589 := by norm_num
private theorem prime_sixtyFourBJ_71593 : Nat.Prime 71593 := by norm_num
private theorem prime_sixtyFourBJ_74941 : Nat.Prime 74941 := by norm_num
private theorem prime_sixtyFourBJ_75337 : Nat.Prime 75337 := by norm_num
private theorem prime_sixtyFourBJ_75377 : Nat.Prime 75377 := by norm_num
private theorem prime_sixtyFourBJ_79537 : Nat.Prime 79537 := by norm_num
private theorem prime_sixtyFourBJ_81563 : Nat.Prime 81563 := by norm_num
private theorem prime_sixtyFourBJ_83621 : Nat.Prime 83621 := by norm_num
private theorem prime_sixtyFourBJ_84761 : Nat.Prime 84761 := by norm_num
private theorem prime_sixtyFourBJ_89939 : Nat.Prime 89939 := by norm_num
private theorem prime_sixtyFourBJ_93337 : Nat.Prime 93337 := by norm_num
private theorem prime_sixtyFourBJ_98947 : Nat.Prime 98947 := by norm_num
private theorem prime_sixtyFourBJ_103549 : Nat.Prime 103549 := by norm_num
private theorem prime_sixtyFourBJ_107581 : Nat.Prime 107581 := by norm_num
private theorem prime_sixtyFourBJ_109229 : Nat.Prime 109229 := by norm_num
private theorem prime_sixtyFourBJ_109849 : Nat.Prime 109849 := by norm_num
private theorem prime_sixtyFourBJ_119771 : Nat.Prime 119771 := by norm_num
private theorem prime_sixtyFourBJ_119813 : Nat.Prime 119813 := by norm_num
private theorem prime_sixtyFourBJ_125789 : Nat.Prime 125789 := by norm_num
private theorem prime_sixtyFourBJ_126023 : Nat.Prime 126023 := by norm_num
private theorem prime_sixtyFourBJ_129313 : Nat.Prime 129313 := by norm_num
private theorem prime_sixtyFourBJ_131071 : Nat.Prime 131071 := by norm_num
private theorem prime_sixtyFourBJ_134177 : Nat.Prime 134177 := by norm_num
private theorem prime_sixtyFourBJ_141073 : Nat.Prime 141073 := by norm_num
private theorem prime_sixtyFourBJ_144899 : Nat.Prime 144899 := by norm_num
private theorem prime_sixtyFourBJ_170899 : Nat.Prime 170899 := by norm_num
private theorem prime_sixtyFourBJ_172321 : Nat.Prime 172321 := by norm_num
private theorem prime_sixtyFourBJ_176791 : Nat.Prime 176791 := by norm_num
private theorem prime_sixtyFourBJ_178403 : Nat.Prime 178403 := by norm_num
private theorem prime_sixtyFourBJ_179527 : Nat.Prime 179527 := by norm_num
private theorem prime_sixtyFourBJ_193937 : Nat.Prime 193937 := by norm_num
private theorem prime_sixtyFourBJ_194713 : Nat.Prime 194713 := by norm_num
private theorem prime_sixtyFourBJ_197957 : Nat.Prime 197957 := by norm_num
private theorem prime_sixtyFourBJ_198013 : Nat.Prime 198013 := by norm_num
private theorem prime_sixtyFourBJ_201107 : Nat.Prime 201107 := by norm_num
private theorem prime_sixtyFourBJ_214003 : Nat.Prime 214003 := by norm_num
private theorem prime_sixtyFourBJ_216523 : Nat.Prime 216523 := by norm_num
private theorem prime_sixtyFourBJ_216569 : Nat.Prime 216569 := by norm_num
private theorem prime_sixtyFourBJ_226871 : Nat.Prime 226871 := by norm_num
private theorem prime_sixtyFourBJ_232643 : Nat.Prime 232643 := by norm_num
private theorem prime_sixtyFourBJ_239521 : Nat.Prime 239521 := by norm_num
private theorem prime_sixtyFourBJ_239597 : Nat.Prime 239597 := by norm_num
private theorem prime_sixtyFourBJ_276487 : Nat.Prime 276487 := by norm_num
private theorem prime_sixtyFourBJ_284633 : Nat.Prime 284633 := by norm_num
private theorem prime_sixtyFourBJ_305821 : Nat.Prime 305821 := by norm_num
private theorem prime_sixtyFourBJ_315059 : Nat.Prime 315059 := by norm_num
private theorem prime_sixtyFourBJ_318403 : Nat.Prime 318403 := by norm_num
private theorem prime_sixtyFourBJ_325729 : Nat.Prime 325729 := by norm_num
private theorem prime_sixtyFourBJ_328543 : Nat.Prime 328543 := by norm_num
private theorem prime_sixtyFourBJ_331339 : Nat.Prime 331339 := by norm_num
private theorem prime_sixtyFourBJ_342989 : Nat.Prime 342989 := by norm_num
private theorem prime_sixtyFourBJ_351223 : Nat.Prime 351223 := by norm_num
private theorem prime_sixtyFourBJ_392143 : Nat.Prime 392143 := by norm_num
private theorem prime_sixtyFourBJ_397543 : Nat.Prime 397543 := by norm_num
private theorem prime_sixtyFourBJ_398611 : Nat.Prime 398611 := by norm_num
private theorem prime_sixtyFourBJ_403063 : Nat.Prime 403063 := by norm_num
private theorem prime_sixtyFourBJ_404983 : Nat.Prime 404983 := by norm_num
private theorem prime_sixtyFourBJ_410233 : Nat.Prime 410233 := by norm_num
private theorem prime_sixtyFourBJ_413429 : Nat.Prime 413429 := by norm_num
private theorem prime_sixtyFourBJ_460813 : Nat.Prime 460813 := by norm_num
private theorem prime_sixtyFourBJ_466171 : Nat.Prime 466171 := by norm_num
private theorem prime_sixtyFourBJ_474757 : Nat.Prime 474757 := by norm_num
private theorem prime_sixtyFourBJ_487187 : Nat.Prime 487187 := by norm_num
private theorem prime_sixtyFourBJ_495433 : Nat.Prime 495433 := by norm_num
private theorem prime_sixtyFourBJ_511579 : Nat.Prime 511579 := by norm_num
private theorem prime_sixtyFourBJ_520853 : Nat.Prime 520853 := by norm_num
private theorem prime_sixtyFourBJ_521173 : Nat.Prime 521173 := by norm_num
private theorem prime_sixtyFourBJ_522061 : Nat.Prime 522061 := by norm_num
private theorem prime_sixtyFourBJ_606379 : Nat.Prime 606379 := by norm_num
private theorem prime_sixtyFourBJ_617453 : Nat.Prime 617453 := by norm_num
private theorem prime_sixtyFourBJ_617521 : Nat.Prime 617521 := by norm_num
private theorem prime_sixtyFourBJ_629857 : Nat.Prime 629857 := by norm_num
private theorem prime_sixtyFourBJ_641371 : Nat.Prime 641371 := by norm_num
private theorem prime_sixtyFourBJ_681523 : Nat.Prime 681523 := by norm_num
private theorem prime_sixtyFourBJ_682697 : Nat.Prime 682697 := by norm_num
private theorem prime_sixtyFourBJ_683957 : Nat.Prime 683957 := by norm_num
private theorem prime_sixtyFourBJ_741599 : Nat.Prime 741599 := by norm_num
private theorem prime_sixtyFourBJ_780047 : Nat.Prime 780047 := by norm_num
private theorem prime_sixtyFourBJ_834653 : Nat.Prime 834653 := by norm_num
private theorem prime_sixtyFourBJ_912007 : Nat.Prime 912007 := by norm_num
private theorem prime_sixtyFourBJ_921901 : Nat.Prime 921901 := by norm_num
private theorem prime_sixtyFourBJ_937171 : Nat.Prime 937171 := by norm_num
private theorem prime_sixtyFourBJ_966521 : Nat.Prime 966521 := by norm_num
private theorem prime_sixtyFourBJ_980299 : Nat.Prime 980299 := by norm_num
private theorem prime_sixtyFourBJ_1031279 : Nat.Prime 1031279 := by norm_num
private theorem prime_sixtyFourBJ_1049549 : Nat.Prime 1049549 := by norm_num
private theorem prime_sixtyFourBJ_1095961 : Nat.Prime 1095961 := by norm_num
private theorem prime_sixtyFourBJ_1097051 : Nat.Prime 1097051 := by norm_num
private theorem prime_sixtyFourBJ_1158401 : Nat.Prime 1158401 := by norm_num
private theorem prime_sixtyFourBJ_1291931 : Nat.Prime 1291931 := by norm_num
private theorem prime_sixtyFourBJ_1414331 : Nat.Prime 1414331 := by norm_num
private theorem prime_sixtyFourBJ_1545949 : Nat.Prime 1545949 := by norm_num
private theorem prime_sixtyFourBJ_1569157 : Nat.Prime 1569157 := by norm_num
private theorem prime_sixtyFourBJ_1658963 : Nat.Prime 1658963 := by norm_num
private theorem prime_sixtyFourBJ_1662943 : Nat.Prime 1662943 := by norm_num
private theorem prime_sixtyFourBJ_1886659 : Nat.Prime 1886659 := by norm_num
private theorem prime_sixtyFourBJ_1900433 : Nat.Prime 1900433 := by norm_num
private theorem prime_sixtyFourBJ_2029981 : Nat.Prime 2029981 := by norm_num
private theorem prime_sixtyFourBJ_2111251 : Nat.Prime 2111251 := by norm_num
private theorem prime_sixtyFourBJ_2417201 : Nat.Prime 2417201 := by norm_num
private theorem prime_sixtyFourBJ_2425453 : Nat.Prime 2425453 := by norm_num
private theorem prime_sixtyFourBJ_2589607 : Nat.Prime 2589607 := by norm_num
private theorem prime_sixtyFourBJ_2643659 : Nat.Prime 2643659 := by norm_num
private theorem prime_sixtyFourBJ_2706059 : Nat.Prime 2706059 := by norm_num
private theorem prime_sixtyFourBJ_2808023 : Nat.Prime 2808023 := by norm_num
private theorem prime_sixtyFourBJ_2950813 : Nat.Prime 2950813 := by norm_num
private theorem prime_sixtyFourBJ_2970791 : Nat.Prime 2970791 := by norm_num
private theorem prime_sixtyFourBJ_3133751 : Nat.Prime 3133751 := by norm_num
private theorem prime_sixtyFourBJ_3463729 : Nat.Prime 3463729 := by norm_num
private theorem prime_sixtyFourBJ_3785569 : Nat.Prime 3785569 := by norm_num
private theorem prime_sixtyFourBJ_3947921 : Nat.Prime 3947921 := by norm_num
private theorem prime_sixtyFourBJ_4057553 : Nat.Prime 4057553 := by norm_num
private theorem prime_sixtyFourBJ_4309363 : Nat.Prime 4309363 := by norm_num
private theorem prime_sixtyFourBJ_4368809 : Nat.Prime 4368809 := by norm_num
private theorem prime_sixtyFourBJ_4444789 : Nat.Prime 4444789 := by norm_num
private theorem prime_sixtyFourBJ_4449409 : Nat.Prime 4449409 := by norm_num
private theorem prime_sixtyFourBJ_4599857 : Nat.Prime 4599857 := by norm_num
private theorem prime_sixtyFourBJ_4776113 : Nat.Prime 4776113 := by norm_num
private theorem prime_sixtyFourBJ_4794733 : Nat.Prime 4794733 := by norm_num
private theorem prime_sixtyFourBJ_4919573 : Nat.Prime 4919573 := by norm_num
private theorem prime_sixtyFourBJ_5095333 : Nat.Prime 5095333 := by norm_num
private theorem prime_sixtyFourBJ_5181217 : Nat.Prime 5181217 := by norm_num
private theorem prime_sixtyFourBJ_5457773 : Nat.Prime 5457773 := by norm_num
private theorem prime_sixtyFourBJ_5715433 : Nat.Prime 5715433 := by norm_num
private theorem prime_sixtyFourBJ_5734231 : Nat.Prime 5734231 := by norm_num
private theorem prime_sixtyFourBJ_5911709 : Nat.Prime 5911709 := by norm_num
private theorem prime_sixtyFourBJ_5961353 : Nat.Prime 5961353 := by norm_num
private theorem prime_sixtyFourBJ_6239053 : Nat.Prime 6239053 := by norm_num
private theorem prime_sixtyFourBJ_6763369 : Nat.Prime 6763369 := by norm_num
private theorem prime_sixtyFourBJ_7021229 : Nat.Prime 7021229 := by norm_num
private theorem prime_sixtyFourBJ_7417691 : Nat.Prime 7417691 := by norm_num
private theorem prime_sixtyFourBJ_7420951 : Nat.Prime 7420951 := by norm_num
private theorem prime_sixtyFourBJ_7486711 : Nat.Prime 7486711 := by norm_num
private theorem prime_sixtyFourBJ_8006179 : Nat.Prime 8006179 := by norm_num
private theorem prime_sixtyFourBJ_8261443 : Nat.Prime 8261443 := by norm_num
private theorem prime_sixtyFourBJ_8391517 : Nat.Prime 8391517 := by norm_num
private theorem prime_sixtyFourBJ_8807563 : Nat.Prime 8807563 := by norm_num
private theorem prime_sixtyFourBJ_8879993 : Nat.Prime 8879993 := by norm_num
private theorem prime_sixtyFourBJ_9267619 : Nat.Prime 9267619 := by norm_num
private theorem prime_sixtyFourBJ_9603203 : Nat.Prime 9603203 := by norm_num
private theorem prime_sixtyFourBJ_9698713 : Nat.Prime 9698713 := by norm_num
private theorem prime_sixtyFourBJ_9767977 : Nat.Prime 9767977 := by norm_num
private theorem prime_sixtyFourBJ_9975223 : Nat.Prime 9975223 := by norm_num
private theorem prime_sixtyFourBJ_10607227 : Nat.Prime 10607227 := by norm_num
private theorem prime_sixtyFourBJ_11580817 : Nat.Prime 11580817 := by norm_num
private theorem prime_sixtyFourBJ_12084221 : Nat.Prime 12084221 := by norm_num
private theorem prime_sixtyFourBJ_13260067 : Nat.Prime 13260067 := by norm_num
private theorem prime_sixtyFourBJ_13902587 : Nat.Prime 13902587 := by norm_num
private theorem prime_sixtyFourBJ_13922939 : Nat.Prime 13922939 := by norm_num
private theorem prime_sixtyFourBJ_14405701 : Nat.Prime 14405701 := by norm_num
private theorem prime_sixtyFourBJ_16162739 : Nat.Prime 16162739 := by norm_num
private theorem prime_sixtyFourBJ_17044847 : Nat.Prime 17044847 := by norm_num
private theorem prime_sixtyFourBJ_17107637 : Nat.Prime 17107637 := by norm_num
private theorem prime_sixtyFourBJ_17772977 : Nat.Prime 17772977 := by norm_num
private theorem prime_sixtyFourBJ_19222561 : Nat.Prime 19222561 := by norm_num
private theorem prime_sixtyFourBJ_19717343 : Nat.Prime 19717343 := by norm_num
private theorem prime_sixtyFourBJ_20239853 : Nat.Prime 20239853 := by norm_num
private theorem prime_sixtyFourBJ_20919757 : Nat.Prime 20919757 := by norm_num
private theorem prime_sixtyFourBJ_21122939 : Nat.Prime 21122939 := by norm_num
private theorem prime_sixtyFourBJ_22600849 : Nat.Prime 22600849 := by norm_num
private theorem prime_sixtyFourBJ_24904721 : Nat.Prime 24904721 := by norm_num
private theorem prime_sixtyFourBJ_33566069 : Nat.Prime 33566069 := by
  apply lucas_primality 33566069 (2 : ZMod 33566069)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8391517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8391517, 1)] : List FactorBlock).map factorBlockValue).prod) = 33566069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_8391517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33566069) ^ 16783034 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33566069) ^ 4 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_33696277 : Nat.Prime 33696277 := by
  apply lucas_primality 33696277 (5 : ZMod 33696277)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2808023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2808023, 1)] : List FactorBlock).map factorBlockValue).prod) = 33696277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_2808023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33696277) ^ 16848138 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 33696277) ^ 11232092 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 33696277) ^ 12 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_36287689 : Nat.Prime 36287689 := by
  apply lucas_primality 36287689 (23 : ZMod 36287689)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (263, 1), (5749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (263, 1), (5749, 1)] : List FactorBlock).map factorBlockValue).prod) = 36287689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_263
      · exact prime_sixtyFourBJ_5749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 36287689) ^ 18143844 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 36287689) ^ 12095896 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 36287689) ^ 137976 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 36287689) ^ 6312 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_41980537 : Nat.Prime 41980537 := by
  apply lucas_primality 41980537 (5 : ZMod 41980537)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (44851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (44851, 1)] : List FactorBlock).map factorBlockValue).prod) = 41980537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_44851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 41980537) ^ 20990268 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 41980537) ^ 13993512 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 41980537) ^ 3229272 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 41980537) ^ 936 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_50758837 : Nat.Prime 50758837 := by
  apply lucas_primality 50758837 (2 : ZMod 50758837)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (47527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (47527, 1)] : List FactorBlock).map factorBlockValue).prod) = 50758837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_89
      · exact prime_sixtyFourBJ_47527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50758837) ^ 25379418 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50758837) ^ 16919612 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50758837) ^ 570324 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50758837) ^ 1068 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_51601609 : Nat.Prime 51601609 := by
  apply lucas_primality 51601609 (13 : ZMod 51601609)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (31, 1), (61, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (31, 1), (61, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 51601609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_31
      · exact prime_sixtyFourBJ_61
      · exact prime_sixtyFourBJ_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 51601609) ^ 25800804 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 51601609) ^ 17200536 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 51601609) ^ 1664568 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 51601609) ^ 845928 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 51601609) ^ 136152 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_54591319 : Nat.Prime 54591319 := by
  apply lucas_primality 54591319 (3 : ZMod 54591319)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (178403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (178403, 1)] : List FactorBlock).map factorBlockValue).prod) = 54591319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_178403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54591319) ^ 27295659 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 54591319) ^ 18197106 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 54591319) ^ 3211254 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 54591319) ^ 306 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_58120199 : Nat.Prime 58120199 := by
  apply lucas_primality 58120199 (7 : ZMod 58120199)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3023, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3023, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) = 58120199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3023
      · exact prime_sixtyFourBJ_9613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 58120199) ^ 29060099 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 58120199) ^ 19226 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 58120199) ^ 6046 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_66092629 : Nat.Prime 66092629 := by
  apply lucas_primality 66092629 (2 : ZMod 66092629)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (103, 1), (7639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (103, 1), (7639, 1)] : List FactorBlock).map factorBlockValue).prod) = 66092629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_103
      · exact prime_sixtyFourBJ_7639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66092629) ^ 33046314 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 66092629) ^ 22030876 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 66092629) ^ 9441804 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 66092629) ^ 641676 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 66092629) ^ 8652 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_67132139 : Nat.Prime 67132139 := by
  apply lucas_primality 67132139 (2 : ZMod 67132139)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33566069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33566069, 1)] : List FactorBlock).map factorBlockValue).prod) = 67132139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_33566069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 67132139) ^ 33566069 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 67132139) ^ 2 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_75109709 : Nat.Prime 75109709 := by
  apply lucas_primality 75109709 (2 : ZMod 75109709)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (126023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (126023, 1)] : List FactorBlock).map factorBlockValue).prod) = 75109709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_149
      · exact prime_sixtyFourBJ_126023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75109709) ^ 37554854 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75109709) ^ 504092 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75109709) ^ 596 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_76715729 : Nat.Prime 76715729 := by
  apply lucas_primality 76715729 (3 : ZMod 76715729)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4794733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4794733, 1)] : List FactorBlock).map factorBlockValue).prod) = 76715729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_4794733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 76715729) ^ 38357864 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 76715729) ^ 16 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_81833341 : Nat.Prime 81833341 := by
  apply lucas_primality 81833341 (10 : ZMod 81833341)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (167, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (167, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) = 81833341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_167
      · exact prime_sixtyFourBJ_8167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 81833341) ^ 40916670 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 81833341) ^ 27277780 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 81833341) ^ 16366668 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 81833341) ^ 490020 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 81833341) ^ 10020 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_83415523 : Nat.Prime 83415523 := by
  apply lucas_primality 83415523 (2 : ZMod 83415523)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13902587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13902587, 1)] : List FactorBlock).map factorBlockValue).prod) = 83415523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13902587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 83415523) ^ 41707761 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83415523) ^ 27805174 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83415523) ^ 6 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_84254749 : Nat.Prime 84254749 := by
  apply lucas_primality 84254749 (7 : ZMod 84254749)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7021229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7021229, 1)] : List FactorBlock).map factorBlockValue).prod) = 84254749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7021229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 84254749) ^ 42127374 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 84254749) ^ 28084916 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 84254749) ^ 12 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_85390729 : Nat.Prime 85390729 := by
  apply lucas_primality 85390729 (13 : ZMod 85390729)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (47, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (47, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 85390729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_47
      · exact prime_sixtyFourBJ_61
      · exact prime_sixtyFourBJ_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 85390729) ^ 42695364 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 85390729) ^ 28463576 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 85390729) ^ 5022984 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 85390729) ^ 1816824 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 85390729) ^ 1399848 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 85390729) ^ 1169736 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_94165727 : Nat.Prime 94165727 := by
  apply lucas_primality 94165727 (5 : ZMod 94165727)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (29, 1), (70589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (29, 1), (70589, 1)] : List FactorBlock).map factorBlockValue).prod) = 94165727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_70589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 94165727) ^ 47082863 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 94165727) ^ 4094162 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 94165727) ^ 3247094 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 94165727) ^ 1334 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_101340049 : Nat.Prime 101340049 := by
  apply lucas_primality 101340049 (7 : ZMod 101340049)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2111251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2111251, 1)] : List FactorBlock).map factorBlockValue).prod) = 101340049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_2111251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 101340049) ^ 50670024 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 101340049) ^ 33780016 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 101340049) ^ 48 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_105213599 : Nat.Prime 105213599 := by
  apply lucas_primality 105213599 (7 : ZMod 105213599)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (751, 1), (10007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (751, 1), (10007, 1)] : List FactorBlock).map factorBlockValue).prod) = 105213599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_751
      · exact prime_sixtyFourBJ_10007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 105213599) ^ 52606799 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 105213599) ^ 15030514 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 105213599) ^ 140098 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 105213599) ^ 10514 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_106514801 : Nat.Prime 106514801 := by
  apply lucas_primality 106514801 (3 : ZMod 106514801)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (109, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (109, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) = 106514801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_109
      · exact prime_sixtyFourBJ_349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 106514801) ^ 53257400 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106514801) ^ 21302960 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106514801) ^ 15216400 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106514801) ^ 977200 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 106514801) ^ 305200 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_106559917 : Nat.Prime 106559917 := by
  apply lucas_primality 106559917 (2 : ZMod 106559917)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8879993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8879993, 1)] : List FactorBlock).map factorBlockValue).prod) = 106559917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_8879993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106559917) ^ 53279958 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 106559917) ^ 35519972 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 106559917) ^ 12 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_110337977 : Nat.Prime 110337977 := by
  apply lucas_primality 110337977 (3 : ZMod 110337977)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (71, 1), (27751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (71, 1), (27751, 1)] : List FactorBlock).map factorBlockValue).prod) = 110337977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_71
      · exact prime_sixtyFourBJ_27751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 110337977) ^ 55168988 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 110337977) ^ 15762568 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 110337977) ^ 1554056 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 110337977) ^ 3976 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_121904933 : Nat.Prime 121904933 := by
  apply lucas_primality 121904933 (2 : ZMod 121904933)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (232643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (232643, 1)] : List FactorBlock).map factorBlockValue).prod) = 121904933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_131
      · exact prime_sixtyFourBJ_232643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 121904933) ^ 60952466 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121904933) ^ 930572 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121904933) ^ 524 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_122488559 : Nat.Prime 122488559 := by
  apply lucas_primality 122488559 (7 : ZMod 122488559)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (606379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (606379, 1)] : List FactorBlock).map factorBlockValue).prod) = 122488559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_101
      · exact prime_sixtyFourBJ_606379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 122488559) ^ 61244279 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 122488559) ^ 1212758 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 122488559) ^ 202 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_128047627 : Nat.Prime 128047627 := by
  apply lucas_primality 128047627 (2 : ZMod 128047627)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (433, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (433, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) = 128047627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_433
      · exact prime_sixtyFourBJ_2347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 128047627) ^ 64023813 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 128047627) ^ 42682542 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 128047627) ^ 18292518 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 128047627) ^ 295722 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 128047627) ^ 54558 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_129006791 : Nat.Prime 129006791 := by
  apply lucas_primality 129006791 (7 : ZMod 129006791)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (29, 1), (37, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (29, 1), (37, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 129006791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_37
      · exact prime_sixtyFourBJ_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 129006791) ^ 64503395 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 129006791) ^ 25801358 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 129006791) ^ 11727890 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 129006791) ^ 4448510 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 129006791) ^ 3486670 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 129006791) ^ 118030 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_130515251 : Nat.Prime 130515251 := by
  apply lucas_primality 130515251 (2 : ZMod 130515251)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (522061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (522061, 1)] : List FactorBlock).map factorBlockValue).prod) = 130515251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_522061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 130515251) ^ 65257625 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 130515251) ^ 26103050 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 130515251) ^ 250 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_160322003 : Nat.Prime 160322003 := by
  apply lucas_primality 160322003 (2 : ZMod 160322003)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (757, 1), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (757, 1), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) = 160322003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_757
      · exact prime_sixtyFourBJ_6229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 160322003) ^ 80161001 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 160322003) ^ 9430706 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 160322003) ^ 211786 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 160322003) ^ 25738 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_183038131 : Nat.Prime 183038131 := by
  apply lucas_primality 183038131 (2 : ZMod 183038131)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (11, 1), (20543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (11, 1), (20543, 1)] : List FactorBlock).map factorBlockValue).prod) = 183038131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_20543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 183038131) ^ 91519065 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 183038131) ^ 61012710 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 183038131) ^ 36607626 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 183038131) ^ 16639830 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 183038131) ^ 8910 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_190554941 : Nat.Prime 190554941 := by
  apply lucas_primality 190554941 (3 : ZMod 190554941)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (328543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (328543, 1)] : List FactorBlock).map factorBlockValue).prod) = 190554941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_328543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 190554941) ^ 95277470 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 190554941) ^ 38110988 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 190554941) ^ 6570860 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 190554941) ^ 580 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_198230699 : Nat.Prime 198230699 := by
  apply lucas_primality 198230699 (2 : ZMod 198230699)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (4309363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (4309363, 1)] : List FactorBlock).map factorBlockValue).prod) = 198230699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_4309363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 198230699) ^ 99115349 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198230699) ^ 8618726 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198230699) ^ 46 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_209702833 : Nat.Prime 209702833 := by
  apply lucas_primality 209702833 (5 : ZMod 209702833)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (4368809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (4368809, 1)] : List FactorBlock).map factorBlockValue).prod) = 209702833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_4368809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 209702833) ^ 104851416 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 209702833) ^ 69900944 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 209702833) ^ 48 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_215149157 : Nat.Prime 215149157 := by
  apply lucas_primality 215149157 (2 : ZMod 215149157)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2693, 1), (19973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2693, 1), (19973, 1)] : List FactorBlock).map factorBlockValue).prod) = 215149157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_2693
      · exact prime_sixtyFourBJ_19973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215149157) ^ 107574578 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 215149157) ^ 79892 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 215149157) ^ 10772 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_230611841 : Nat.Prime 230611841 := by
  apply lucas_primality 230611841 (6 : ZMod 230611841)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (193, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (193, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) = 230611841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_193
      · exact prime_sixtyFourBJ_1867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 230611841) ^ 115305920 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 230611841) ^ 46122368 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 230611841) ^ 1194880 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 230611841) ^ 123520 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_249683279 : Nat.Prime 249683279 := by
  apply lucas_primality 249683279 (19 : ZMod 249683279)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (9603203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (9603203, 1)] : List FactorBlock).map factorBlockValue).prod) = 249683279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_9603203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 249683279) ^ 124841639 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (19 : ZMod 249683279) ^ 19206406 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (19 : ZMod 249683279) ^ 26 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_271210189 : Nat.Prime 271210189 := by
  apply lucas_primality 271210189 (2 : ZMod 271210189)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (22600849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (22600849, 1)] : List FactorBlock).map factorBlockValue).prod) = 271210189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_22600849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 271210189) ^ 135605094 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 271210189) ^ 90403396 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 271210189) ^ 12 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_272210087 : Nat.Prime 272210087 := by
  apply lucas_primality 272210087 (5 : ZMod 272210087)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (8006179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (8006179, 1)] : List FactorBlock).map factorBlockValue).prod) = 272210087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_8006179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 272210087) ^ 136105043 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 272210087) ^ 16012358 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 272210087) ^ 34 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_274940537 : Nat.Prime 274940537 := by
  apply lucas_primality 274940537 (5 : ZMod 274940537)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (2643659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (2643659, 1)] : List FactorBlock).map factorBlockValue).prod) = 274940537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_2643659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 274940537) ^ 137470268 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 274940537) ^ 21149272 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 274940537) ^ 104 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_321912683 : Nat.Prime 321912683 := by
  apply lucas_primality 321912683 (2 : ZMod 321912683)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (47, 1), (37633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (47, 1), (37633, 1)] : List FactorBlock).map factorBlockValue).prod) = 321912683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_47
      · exact prime_sixtyFourBJ_37633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 321912683) ^ 160956341 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 321912683) ^ 45987526 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 321912683) ^ 24762514 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 321912683) ^ 6849206 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 321912683) ^ 8554 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_353851483 : Nat.Prime 353851483 := by
  apply lucas_primality 353851483 (5 : ZMod 353851483)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3739, 1), (15773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3739, 1), (15773, 1)] : List FactorBlock).map factorBlockValue).prod) = 353851483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_3739
      · exact prime_sixtyFourBJ_15773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 353851483) ^ 176925741 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 353851483) ^ 117950494 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 353851483) ^ 94638 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 353851483) ^ 22434 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_355274723 : Nat.Prime 355274723 := by
  apply lucas_primality 355274723 (2 : ZMod 355274723)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (97, 1), (229, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (97, 1), (229, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod) = 355274723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_97
      · exact prime_sixtyFourBJ_229
      · exact prime_sixtyFourBJ_727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355274723) ^ 177637361 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 355274723) ^ 32297702 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 355274723) ^ 3662626 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 355274723) ^ 1551418 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 355274723) ^ 488686 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_393882239 : Nat.Prime 393882239 := by
  apply lucas_primality 393882239 (7 : ZMod 393882239)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1097, 1), (179527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1097, 1), (179527, 1)] : List FactorBlock).map factorBlockValue).prod) = 393882239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_1097
      · exact prime_sixtyFourBJ_179527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 393882239) ^ 196941119 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 393882239) ^ 359054 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 393882239) ^ 2194 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_398144713 : Nat.Prime 398144713 := by
  apply lucas_primality 398144713 (5 : ZMod 398144713)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (29, 1), (71, 1), (1151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (29, 1), (71, 1), (1151, 1)] : List FactorBlock).map factorBlockValue).prod) = 398144713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_71
      · exact prime_sixtyFourBJ_1151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 398144713) ^ 199072356 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 398144713) ^ 132714904 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 398144713) ^ 56877816 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 398144713) ^ 13729128 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 398144713) ^ 5607672 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 398144713) ^ 345912 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_418502137 : Nat.Prime 418502137 := by
  apply lucas_primality 418502137 (5 : ZMod 418502137)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 3), (7937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 3), (7937, 1)] : List FactorBlock).map factorBlockValue).prod) = 418502137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_7937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 418502137) ^ 209251068 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 418502137) ^ 139500712 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 418502137) ^ 32192472 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 418502137) ^ 52728 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_591447133 : Nat.Prime 591447133 := by
  apply lucas_primality 591447133 (6 : ZMod 591447133)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (337, 1), (48751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (337, 1), (48751, 1)] : List FactorBlock).map factorBlockValue).prod) = 591447133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_337
      · exact prime_sixtyFourBJ_48751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 591447133) ^ 295723566 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 591447133) ^ 197149044 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 591447133) ^ 1755036 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 591447133) ^ 12132 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_809665177 : Nat.Prime 809665177 := by
  apply lucas_primality 809665177 (5 : ZMod 809665177)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1051, 1), (32099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1051, 1), (32099, 1)] : List FactorBlock).map factorBlockValue).prod) = 809665177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_1051
      · exact prime_sixtyFourBJ_32099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 809665177) ^ 404832588 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 809665177) ^ 269888392 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 809665177) ^ 770376 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 809665177) ^ 25224 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_922217641 : Nat.Prime 922217641 := by
  apply lucas_primality 922217641 (13 : ZMod 922217641)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (941, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (941, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) = 922217641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_941
      · exact prime_sixtyFourBJ_8167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 922217641) ^ 461108820 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 922217641) ^ 307405880 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 922217641) ^ 184443528 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 922217641) ^ 980040 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 922217641) ^ 112920 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_928620083 : Nat.Prime 928620083 := by
  apply lucas_primality 928620083 (2 : ZMod 928620083)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (563, 1), (63439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (563, 1), (63439, 1)] : List FactorBlock).map factorBlockValue).prod) = 928620083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_563
      · exact prime_sixtyFourBJ_63439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 928620083) ^ 464310041 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 928620083) ^ 71432314 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 928620083) ^ 1649414 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 928620083) ^ 14638 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1029403787 : Nat.Prime 1029403787 := by
  apply lucas_primality 1029403787 (2 : ZMod 1029403787)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (1399, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (1399, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1029403787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_233
      · exact prime_sixtyFourBJ_1399
      · exact prime_sixtyFourBJ_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1029403787) ^ 514701893 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1029403787) ^ 4418042 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1029403787) ^ 735814 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1029403787) ^ 651934 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1216080589 : Nat.Prime 1216080589 := by
  apply lucas_primality 1216080589 (6 : ZMod 1216080589)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101340049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101340049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1216080589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_101340049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1216080589) ^ 608040294 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1216080589) ^ 405360196 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1216080589) ^ 12 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1258574221 : Nat.Prime 1258574221 := by
  apply lucas_primality 1258574221 (2 : ZMod 1258574221)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (983, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (983, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1258574221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_983
      · exact prime_sixtyFourBJ_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1258574221) ^ 629287110 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1258574221) ^ 419524740 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1258574221) ^ 251714844 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1258574221) ^ 1280340 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1258574221) ^ 530820 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1342642781 : Nat.Prime 1342642781 := by
  apply lucas_primality 1342642781 (2 : ZMod 1342642781)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (67132139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (67132139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1342642781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_67132139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1342642781) ^ 671321390 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342642781) ^ 268528556 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342642781) ^ 20 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1405961729 : Nat.Prime 1405961729 := by
  apply lucas_primality 1405961729 (3 : ZMod 1405961729)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (227, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (227, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1405961729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_227
      · exact prime_sixtyFourBJ_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1405961729) ^ 702980864 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1405961729) ^ 6193664 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1405961729) ^ 116224 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1413709321 : Nat.Prime 1413709321 := by
  apply lucas_primality 1413709321 (7 : ZMod 1413709321)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (37, 1), (318403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (37, 1), (318403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1413709321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_37
      · exact prime_sixtyFourBJ_318403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1413709321) ^ 706854660 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1413709321) ^ 471236440 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1413709321) ^ 282741864 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1413709321) ^ 38208360 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1413709321) ^ 4440 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1457137247 : Nat.Prime 1457137247 := by
  apply lucas_primality 1457137247 (5 : ZMod 1457137247)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1367, 1), (28051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1367, 1), (28051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1457137247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_1367
      · exact prime_sixtyFourBJ_28051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1457137247) ^ 728568623 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1457137247) ^ 76691434 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1457137247) ^ 1065938 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1457137247) ^ 51946 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1493291993 : Nat.Prime 1493291993 := by
  apply lucas_primality 1493291993 (3 : ZMod 1493291993)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (181, 1), (1031279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (181, 1), (1031279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1493291993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_181
      · exact prime_sixtyFourBJ_1031279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1493291993) ^ 746645996 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1493291993) ^ 8250232 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1493291993) ^ 1448 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1585845593 : Nat.Prime 1585845593 := by
  apply lucas_primality 1585845593 (3 : ZMod 1585845593)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (198230699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (198230699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585845593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_198230699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1585845593) ^ 792922796 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1585845593) ^ 8 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1634613839 : Nat.Prime 1634613839 := by
  apply lucas_primality 1634613839 (11 : ZMod 1634613839)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (5715433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (5715433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1634613839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_5715433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1634613839) ^ 817306919 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1634613839) ^ 148601258 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1634613839) ^ 125739526 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1634613839) ^ 286 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1656256813 : Nat.Prime 1656256813 := by
  apply lucas_primality 1656256813 (6 : ZMod 1656256813)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19717343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19717343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1656256813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_19717343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1656256813) ^ 828128406 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1656256813) ^ 552085604 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1656256813) ^ 236608116 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1656256813) ^ 84 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1731572501 : Nat.Prime 1731572501 := by
  apply lucas_primality 1731572501 (2 : ZMod 1731572501)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 4), (7, 1), (98947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 4), (7, 1), (98947, 1)] : List FactorBlock).map factorBlockValue).prod) = 1731572501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_98947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1731572501) ^ 865786250 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1731572501) ^ 346314500 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1731572501) ^ 247367500 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1731572501) ^ 17500 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1948838897 : Nat.Prime 1948838897 := by
  apply lucas_primality 1948838897 (3 : ZMod 1948838897)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (2970791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (2970791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1948838897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_41
      · exact prime_sixtyFourBJ_2970791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1948838897) ^ 974419448 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1948838897) ^ 47532656 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1948838897) ^ 656 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1983892909 : Nat.Prime 1983892909 := by
  apply lucas_primality 1983892909 (2 : ZMod 1983892909)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (313, 1), (4159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (313, 1), (4159, 1)] : List FactorBlock).map factorBlockValue).prod) = 1983892909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_127
      · exact prime_sixtyFourBJ_313
      · exact prime_sixtyFourBJ_4159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1983892909) ^ 991946454 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983892909) ^ 661297636 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983892909) ^ 15621204 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983892909) ^ 6338316 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983892909) ^ 477012 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2116138139 : Nat.Prime 2116138139 := by
  apply lucas_primality 2116138139 (2 : ZMod 2116138139)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (2706059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (2706059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2116138139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_2706059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2116138139) ^ 1058069069 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2116138139) ^ 124478714 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2116138139) ^ 92006006 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2116138139) ^ 782 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2160042449 : Nat.Prime 2160042449 := by
  apply lucas_primality 2160042449 (3 : ZMod 2160042449)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (211, 1), (331, 1), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (211, 1), (331, 1), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) = 2160042449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_211
      · exact prime_sixtyFourBJ_331
      · exact prime_sixtyFourBJ_1933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2160042449) ^ 1080021224 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2160042449) ^ 10237168 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2160042449) ^ 6525808 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2160042449) ^ 1117456 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2199524297 : Nat.Prime 2199524297 := by
  apply lucas_primality 2199524297 (3 : ZMod 2199524297)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (274940537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (274940537, 1)] : List FactorBlock).map factorBlockValue).prod) = 2199524297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_274940537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2199524297) ^ 1099762148 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2199524297) ^ 8 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2205033499 : Nat.Prime 2205033499 := by
  apply lucas_primality 2205033499 (2 : ZMod 2205033499)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (191, 1), (641371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (191, 1), (641371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2205033499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_191
      · exact prime_sixtyFourBJ_641371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2205033499) ^ 1102516749 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2205033499) ^ 735011166 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2205033499) ^ 11544678 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2205033499) ^ 3438 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3194675663 : Nat.Prime 3194675663 := by
  apply lucas_primality 3194675663 (5 : ZMod 3194675663)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (4449409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (4449409, 1)] : List FactorBlock).map factorBlockValue).prod) = 3194675663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_359
      · exact prime_sixtyFourBJ_4449409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3194675663) ^ 1597337831 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3194675663) ^ 8898818 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3194675663) ^ 718 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3506501653 : Nat.Prime 3506501653 := by
  apply lucas_primality 3506501653 (2 : ZMod 3506501653)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1453, 1), (201107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1453, 1), (201107, 1)] : List FactorBlock).map factorBlockValue).prod) = 3506501653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_1453
      · exact prime_sixtyFourBJ_201107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3506501653) ^ 1753250826 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3506501653) ^ 1168833884 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3506501653) ^ 2413284 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3506501653) ^ 17436 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3841375579 : Nat.Prime 3841375579 := by
  apply lucas_primality 3841375579 (3 : ZMod 3841375579)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (33696277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (33696277, 1)] : List FactorBlock).map factorBlockValue).prod) = 3841375579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_33696277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3841375579) ^ 1920687789 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3841375579) ^ 1280458526 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3841375579) ^ 202177662 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3841375579) ^ 114 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_4047562439 : Nat.Prime 4047562439 := by
  apply lucas_primality 4047562439 (7 : ZMod 4047562439)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (106514801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (106514801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4047562439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_106514801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4047562439) ^ 2023781219 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4047562439) ^ 213029602 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4047562439) ^ 38 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_4552201517 : Nat.Prime 4552201517 := by
  apply lucas_primality 4552201517 (2 : ZMod 4552201517)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (14405701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (14405701, 1)] : List FactorBlock).map factorBlockValue).prod) = 4552201517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_79
      · exact prime_sixtyFourBJ_14405701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4552201517) ^ 2276100758 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4552201517) ^ 57622804 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4552201517) ^ 316 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_5574777079 : Nat.Prime 5574777079 := by
  apply lucas_primality 5574777079 (3 : ZMod 5574777079)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2251, 1), (31751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2251, 1), (31751, 1)] : List FactorBlock).map factorBlockValue).prod) = 5574777079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_2251
      · exact prime_sixtyFourBJ_31751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5574777079) ^ 2787388539 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5574777079) ^ 1858259026 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5574777079) ^ 428829006 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5574777079) ^ 2476578 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5574777079) ^ 175578 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_6400119599 : Nat.Prime 6400119599 := by
  apply lucas_primality 6400119599 (11 : ZMod 6400119599)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (151, 1), (401, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (151, 1), (401, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) = 6400119599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_41
      · exact prime_sixtyFourBJ_151
      · exact prime_sixtyFourBJ_401
      · exact prime_sixtyFourBJ_1289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6400119599) ^ 3200059799 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6400119599) ^ 156100478 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6400119599) ^ 42384898 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6400119599) ^ 15960398 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 6400119599) ^ 4965182 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_7034989391 : Nat.Prime 7034989391 := by
  apply lucas_primality 7034989391 (11 : ZMod 7034989391)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (4919573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (4919573, 1)] : List FactorBlock).map factorBlockValue).prod) = 7034989391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_4919573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7034989391) ^ 3517494695 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7034989391) ^ 1406997878 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7034989391) ^ 639544490 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7034989391) ^ 541153030 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 7034989391) ^ 1430 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_8248042681 : Nat.Prime 8248042681 := by
  apply lucas_primality 8248042681 (19 : ZMod 8248042681)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (353, 1), (194713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (353, 1), (194713, 1)] : List FactorBlock).map factorBlockValue).prod) = 8248042681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_353
      · exact prime_sixtyFourBJ_194713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 8248042681) ^ 4124021340 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (19 : ZMod 8248042681) ^ 2749347560 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (19 : ZMod 8248042681) ^ 1649608536 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (19 : ZMod 8248042681) ^ 23365560 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (19 : ZMod 8248042681) ^ 42360 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_10405850401 : Nat.Prime 10405850401 := by
  apply lucas_primality 10405850401 (26 : ZMod 10405850401)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (11, 1), (37, 1), (53, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (11, 1), (37, 1), (53, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) = 10405850401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_37
      · exact prime_sixtyFourBJ_53
      · exact prime_sixtyFourBJ_67
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 10405850401) ^ 5202925200 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (26 : ZMod 10405850401) ^ 3468616800 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (26 : ZMod 10405850401) ^ 2081170080 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (26 : ZMod 10405850401) ^ 945986400 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (26 : ZMod 10405850401) ^ 281239200 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (26 : ZMod 10405850401) ^ 196336800 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (26 : ZMod 10405850401) ^ 155311200 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_12343648393 : Nat.Prime 12343648393 := by
  apply lucas_primality 12343648393 (5 : ZMod 12343648393)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (29, 1), (5911709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (29, 1), (5911709, 1)] : List FactorBlock).map factorBlockValue).prod) = 12343648393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_5911709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12343648393) ^ 6171824196 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12343648393) ^ 4114549464 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12343648393) ^ 425643048 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 12343648393) ^ 2088 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_14810752967 : Nat.Prime 14810752967 := by
  apply lucas_primality 14810752967 (5 : ZMod 14810752967)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (13859, 1), (28123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (13859, 1), (28123, 1)] : List FactorBlock).map factorBlockValue).prod) = 14810752967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_13859
      · exact prime_sixtyFourBJ_28123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14810752967) ^ 7405376483 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14810752967) ^ 779513314 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14810752967) ^ 1068674 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 14810752967) ^ 526642 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_16019726953 : Nat.Prime 16019726953 := by
  apply lucas_primality 16019726953 (5 : ZMod 16019726953)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (131, 1), (5095333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (131, 1), (5095333, 1)] : List FactorBlock).map factorBlockValue).prod) = 16019726953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_131
      · exact prime_sixtyFourBJ_5095333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16019726953) ^ 8009863476 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 16019726953) ^ 5339908984 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 16019726953) ^ 122287992 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 16019726953) ^ 3144 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_17554670531 : Nat.Prime 17554670531 := by
  apply lucas_primality 17554670531 (6 : ZMod 17554670531)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (181, 1), (9698713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (181, 1), (9698713, 1)] : List FactorBlock).map factorBlockValue).prod) = 17554670531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_181
      · exact prime_sixtyFourBJ_9698713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 17554670531) ^ 8777335265 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17554670531) ^ 3510934106 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17554670531) ^ 96987130 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 17554670531) ^ 1810 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_22375512329 : Nat.Prime 22375512329 := by
  apply lucas_primality 22375512329 (3 : ZMod 22375512329)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (215149157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (215149157, 1)] : List FactorBlock).map factorBlockValue).prod) = 22375512329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_215149157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22375512329) ^ 11187756164 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 22375512329) ^ 1721193256 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 22375512329) ^ 104 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_25702359901 : Nat.Prime 25702359901 := by
  apply lucas_primality 25702359901 (6 : ZMod 25702359901)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 1), (43, 1), (284633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 1), (43, 1), (284633, 1)] : List FactorBlock).map factorBlockValue).prod) = 25702359901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_43
      · exact prime_sixtyFourBJ_284633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 25702359901) ^ 12851179950 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25702359901) ^ 8567453300 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25702359901) ^ 5140471980 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25702359901) ^ 3671765700 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25702359901) ^ 597729300 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 25702359901) ^ 90300 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_25938915193 : Nat.Prime 25938915193 := by
  apply lucas_primality 25938915193 (5 : ZMod 25938915193)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (311, 1), (1158401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (311, 1), (1158401, 1)] : List FactorBlock).map factorBlockValue).prod) = 25938915193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_311
      · exact prime_sixtyFourBJ_1158401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 25938915193) ^ 12969457596 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 25938915193) ^ 8646305064 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 25938915193) ^ 83404872 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 25938915193) ^ 22392 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_28463893807 : Nat.Prime 28463893807 := by
  apply lucas_primality 28463893807 (3 : ZMod 28463893807)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (249683279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (249683279, 1)] : List FactorBlock).map factorBlockValue).prod) = 28463893807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_249683279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28463893807) ^ 14231946903 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 28463893807) ^ 9487964602 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 28463893807) ^ 1498099674 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 28463893807) ^ 114 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_29629667777 : Nat.Prime 29629667777 := by
  apply lucas_primality 29629667777 (3 : ZMod 29629667777)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (479, 1), (966521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (479, 1), (966521, 1)] : List FactorBlock).map factorBlockValue).prod) = 29629667777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_479
      · exact prime_sixtyFourBJ_966521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29629667777) ^ 14814833888 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 29629667777) ^ 61857344 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 29629667777) ^ 30656 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_30203577413 : Nat.Prime 30203577413 := by
  apply lucas_primality 30203577413 (2 : ZMod 30203577413)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15241, 1), (495433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15241, 1), (495433, 1)] : List FactorBlock).map factorBlockValue).prod) = 30203577413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_15241
      · exact prime_sixtyFourBJ_495433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30203577413) ^ 15101788706 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30203577413) ^ 1981732 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30203577413) ^ 60964 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_34012072147 : Nat.Prime 34012072147 := by
  apply lucas_primality 34012072147 (3 : ZMod 34012072147)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (29, 1), (43, 1), (89, 1), (3929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (29, 1), (43, 1), (89, 1), (3929, 1)] : List FactorBlock).map factorBlockValue).prod) = 34012072147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_43
      · exact prime_sixtyFourBJ_89
      · exact prime_sixtyFourBJ_3929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34012072147) ^ 17006036073 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34012072147) ^ 11337357382 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34012072147) ^ 2616313242 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34012072147) ^ 1172830074 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34012072147) ^ 790978422 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34012072147) ^ 382158114 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34012072147) ^ 8656674 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_37357444441 : Nat.Prime 37357444441 := by
  apply lucas_primality 37357444441 (17 : ZMod 37357444441)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (251, 1), (413429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (251, 1), (413429, 1)] : List FactorBlock).map factorBlockValue).prod) = 37357444441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_251
      · exact prime_sixtyFourBJ_413429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 37357444441) ^ 18678722220 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 37357444441) ^ 12452481480 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 37357444441) ^ 7471488888 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 37357444441) ^ 148834440 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 37357444441) ^ 90360 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_38249086433 : Nat.Prime 38249086433 := by
  apply lucas_primality 38249086433 (3 : ZMod 38249086433)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (6761, 1), (176791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (6761, 1), (176791, 1)] : List FactorBlock).map factorBlockValue).prod) = 38249086433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_6761
      · exact prime_sixtyFourBJ_176791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38249086433) ^ 19124543216 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 38249086433) ^ 5657312 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 38249086433) ^ 216352 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_46939084333 : Nat.Prime 46939084333 := by
  apply lucas_primality 46939084333 (2 : ZMod 46939084333)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (7993, 1), (69911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (7993, 1), (69911, 1)] : List FactorBlock).map factorBlockValue).prod) = 46939084333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_7993
      · exact prime_sixtyFourBJ_69911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46939084333) ^ 23469542166 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 46939084333) ^ 15646361444 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 46939084333) ^ 6705583476 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 46939084333) ^ 5872524 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 46939084333) ^ 671412 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_47096194517 : Nat.Prime 47096194517 := by
  apply lucas_primality 47096194517 (2 : ZMod 47096194517)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (4789, 1), (351223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (4789, 1), (351223, 1)] : List FactorBlock).map factorBlockValue).prod) = 47096194517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_4789
      · exact prime_sixtyFourBJ_351223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47096194517) ^ 23548097258 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47096194517) ^ 6728027788 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47096194517) ^ 9834244 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47096194517) ^ 134092 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_49509501479 : Nat.Prime 49509501479 := by
  apply lucas_primality 49509501479 (7 : ZMod 49509501479)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1447, 1), (17107637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1447, 1), (17107637, 1)] : List FactorBlock).map factorBlockValue).prod) = 49509501479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_1447
      · exact prime_sixtyFourBJ_17107637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 49509501479) ^ 24754750739 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 49509501479) ^ 34215274 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 49509501479) ^ 2894 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_51992455549 : Nat.Prime 51992455549 := by
  apply lucas_primality 51992455549 (2 : ZMod 51992455549)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (393882239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (393882239, 1)] : List FactorBlock).map factorBlockValue).prod) = 51992455549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_393882239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51992455549) ^ 25996227774 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51992455549) ^ 17330818516 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51992455549) ^ 4726586868 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51992455549) ^ 132 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_65113345639 : Nat.Prime 65113345639 := by
  apply lucas_primality 65113345639 (3 : ZMod 65113345639)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (5501, 1), (19927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (5501, 1), (19927, 1)] : List FactorBlock).map factorBlockValue).prod) = 65113345639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_5501
      · exact prime_sixtyFourBJ_19927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65113345639) ^ 32556672819 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 65113345639) ^ 21704448546 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 65113345639) ^ 5919395058 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 65113345639) ^ 11836638 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 65113345639) ^ 3267594 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_71768644469 : Nat.Prime 71768644469 := by
  apply lucas_primality 71768644469 (2 : ZMod 71768644469)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (103, 1), (157, 1), (15199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (103, 1), (157, 1), (15199, 1)] : List FactorBlock).map factorBlockValue).prod) = 71768644469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_73
      · exact prime_sixtyFourBJ_103
      · exact prime_sixtyFourBJ_157
      · exact prime_sixtyFourBJ_15199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71768644469) ^ 35884322234 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 71768644469) ^ 983132116 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 71768644469) ^ 696782956 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 71768644469) ^ 457125124 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 71768644469) ^ 4721932 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_94381145773 : Nat.Prime 94381145773 := by
  apply lucas_primality 94381145773 (2 : ZMod 94381145773)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (271210189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (271210189, 1)] : List FactorBlock).map factorBlockValue).prod) = 94381145773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_271210189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94381145773) ^ 47190572886 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94381145773) ^ 31460381924 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94381145773) ^ 3254522268 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94381145773) ^ 348 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_115241267371 : Nat.Prime 115241267371 := by
  apply lucas_primality 115241267371 (2 : ZMod 115241267371)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3841375579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3841375579, 1)] : List FactorBlock).map factorBlockValue).prod) = 115241267371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_3841375579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 115241267371) ^ 57620633685 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 115241267371) ^ 38413755790 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 115241267371) ^ 23048253474 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 115241267371) ^ 30 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_125525696297 : Nat.Prime 125525696297 := by
  apply lucas_primality 125525696297 (3 : ZMod 125525696297)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (11, 1), (13, 1), (17, 1), (157, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (11, 1), (13, 1), (17, 1), (157, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 125525696297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_157
      · exact prime_sixtyFourBJ_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 125525696297) ^ 62762848148 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 125525696297) ^ 17932242328 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 125525696297) ^ 11411426936 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 125525696297) ^ 9655822792 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 125525696297) ^ 7383864488 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 125525696297) ^ 799526728 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 125525696297) ^ 149613464 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_146438111623 : Nat.Prime 146438111623 := by
  apply lucas_primality 146438111623 (21 : ZMod 146438111623)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (130515251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (130515251, 1)] : List FactorBlock).map factorBlockValue).prod) = 146438111623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_130515251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 146438111623) ^ 73219055811 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 146438111623) ^ 48812703874 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 146438111623) ^ 13312555602 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 146438111623) ^ 8614006566 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 146438111623) ^ 1122 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_153086609887 : Nat.Prime 153086609887 := by
  apply lucas_primality 153086609887 (5 : ZMod 153086609887)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (281, 1), (682697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (281, 1), (682697, 1)] : List FactorBlock).map factorBlockValue).prod) = 153086609887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_281
      · exact prime_sixtyFourBJ_682697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 153086609887) ^ 76543304943 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 153086609887) ^ 51028869962 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 153086609887) ^ 21869515698 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 153086609887) ^ 8057189994 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 153086609887) ^ 544792206 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 153086609887) ^ 224238 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_168359627797 : Nat.Prime 168359627797 := by
  apply lucas_primality 168359627797 (2 : ZMod 168359627797)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (257, 1), (54591319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (257, 1), (54591319, 1)] : List FactorBlock).map factorBlockValue).prod) = 168359627797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_257
      · exact prime_sixtyFourBJ_54591319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 168359627797) ^ 84179813898 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 168359627797) ^ 56119875932 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 168359627797) ^ 655095828 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 168359627797) ^ 3084 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_218388309409 : Nat.Prime 218388309409 := by
  apply lucas_primality 218388309409 (11 : ZMod 218388309409)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (84254749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (84254749, 1)] : List FactorBlock).map factorBlockValue).prod) = 218388309409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_84254749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 218388309409) ^ 109194154704 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 218388309409) ^ 72796103136 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 218388309409) ^ 2592 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_225576709783 : Nat.Prime 225576709783 := by
  apply lucas_primality 225576709783 (6 : ZMod 225576709783)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1634613839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1634613839, 1)] : List FactorBlock).map factorBlockValue).prod) = 225576709783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_1634613839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 225576709783) ^ 112788354891 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 225576709783) ^ 75192236594 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 225576709783) ^ 9807683034 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 225576709783) ^ 138 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_226941555167 : Nat.Prime 226941555167 := by
  apply lucas_primality 226941555167 (5 : ZMod 226941555167)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5903, 1), (19222561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5903, 1), (19222561, 1)] : List FactorBlock).map factorBlockValue).prod) = 226941555167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5903
      · exact prime_sixtyFourBJ_19222561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 226941555167) ^ 113470777583 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 226941555167) ^ 38445122 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 226941555167) ^ 11806 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_274786070501 : Nat.Prime 274786070501 := by
  apply lucas_primality 274786070501 (2 : ZMod 274786070501)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (17, 1), (257, 1), (125789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (17, 1), (257, 1), (125789, 1)] : List FactorBlock).map factorBlockValue).prod) = 274786070501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_257
      · exact prime_sixtyFourBJ_125789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 274786070501) ^ 137393035250 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 274786070501) ^ 54957214100 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 274786070501) ^ 16163886500 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 274786070501) ^ 1069206500 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 274786070501) ^ 2184500 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_303415791871 : Nat.Prime 303415791871 := by
  apply lucas_primality 303415791871 (3 : ZMod 303415791871)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (75377, 1), (134177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (75377, 1), (134177, 1)] : List FactorBlock).map factorBlockValue).prod) = 303415791871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_75377
      · exact prime_sixtyFourBJ_134177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 303415791871) ^ 151707895935 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 303415791871) ^ 101138597290 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 303415791871) ^ 60683158374 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 303415791871) ^ 4025310 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 303415791871) ^ 2261310 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_309833986261 : Nat.Prime 309833986261 := by
  apply lucas_primality 309833986261 (2 : ZMod 309833986261)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7577, 1), (681523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7577, 1), (681523, 1)] : List FactorBlock).map factorBlockValue).prod) = 309833986261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7577
      · exact prime_sixtyFourBJ_681523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 309833986261) ^ 154916993130 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 309833986261) ^ 103277995420 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 309833986261) ^ 61966797252 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 309833986261) ^ 40891380 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 309833986261) ^ 454620 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_324712149019 : Nat.Prime 324712149019 := by
  apply lucas_primality 324712149019 (10 : ZMod 324712149019)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (1258574221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (1258574221, 1)] : List FactorBlock).map factorBlockValue).prod) = 324712149019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_43
      · exact prime_sixtyFourBJ_1258574221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 324712149019) ^ 162356074509 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 324712149019) ^ 108237383006 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 324712149019) ^ 7551445326 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 324712149019) ^ 258 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_416674392821 : Nat.Prime 416674392821 := by
  apply lucas_primality 416674392821 (2 : ZMod 416674392821)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (71, 1), (1013, 1), (41381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (71, 1), (1013, 1), (41381, 1)] : List FactorBlock).map factorBlockValue).prod) = 416674392821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_71
      · exact prime_sixtyFourBJ_1013
      · exact prime_sixtyFourBJ_41381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 416674392821) ^ 208337196410 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 416674392821) ^ 83334878564 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 416674392821) ^ 59524913260 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 416674392821) ^ 5868653420 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 416674392821) ^ 411327140 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 416674392821) ^ 10069220 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_439783729237 : Nat.Prime 439783729237 := by
  apply lucas_primality 439783729237 (7 : ZMod 439783729237)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (53, 1), (809, 1), (31657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (53, 1), (809, 1), (31657, 1)] : List FactorBlock).map factorBlockValue).prod) = 439783729237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_53
      · exact prime_sixtyFourBJ_809
      · exact prime_sixtyFourBJ_31657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 439783729237) ^ 219891864618 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 439783729237) ^ 146594576412 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 439783729237) ^ 8297806212 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 439783729237) ^ 543614004 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 439783729237) ^ 13892148 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_440711539871 : Nat.Prime 440711539871 := by
  apply lucas_primality 440711539871 (21 : ZMod 440711539871)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (521, 1), (12084221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (521, 1), (12084221, 1)] : List FactorBlock).map factorBlockValue).prod) = 440711539871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_521
      · exact prime_sixtyFourBJ_12084221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 440711539871) ^ 220355769935 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 440711539871) ^ 88142307974 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 440711539871) ^ 62958791410 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 440711539871) ^ 845895470 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (21 : ZMod 440711539871) ^ 36470 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_480591808591 : Nat.Prime 480591808591 := by
  apply lucas_primality 480591808591 (3 : ZMod 480591808591)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (16019726953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (16019726953, 1)] : List FactorBlock).map factorBlockValue).prod) = 480591808591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_16019726953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 480591808591) ^ 240295904295 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 480591808591) ^ 160197269530 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 480591808591) ^ 96118361718 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 480591808591) ^ 30 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_666557013223 : Nat.Prime 666557013223 := by
  apply lucas_primality 666557013223 (3 : ZMod 666557013223)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (12343648393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (12343648393, 1)] : List FactorBlock).map factorBlockValue).prod) = 666557013223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_12343648393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 666557013223) ^ 333278506611 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 666557013223) ^ 222185671074 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 666557013223) ^ 54 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_781360147669 : Nat.Prime 781360147669 := by
  apply lucas_primality 781360147669 (6 : ZMod 781360147669)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (65113345639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (65113345639, 1)] : List FactorBlock).map factorBlockValue).prod) = 781360147669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_65113345639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 781360147669) ^ 390680073834 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 781360147669) ^ 260453382556 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 781360147669) ^ 12 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_783955627529 : Nat.Prime 783955627529 := by
  apply lucas_primality 783955627529 (3 : ZMod 783955627529)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14489, 1), (6763369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14489, 1), (6763369, 1)] : List FactorBlock).map factorBlockValue).prod) = 783955627529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_14489
      · exact prime_sixtyFourBJ_6763369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 783955627529) ^ 391977813764 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 783955627529) ^ 54106952 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 783955627529) ^ 115912 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_914345315861 : Nat.Prime 914345315861 := by
  apply lucas_primality 914345315861 (7 : ZMod 914345315861)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (79, 1), (1693, 1), (20107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (79, 1), (1693, 1), (20107, 1)] : List FactorBlock).map factorBlockValue).prod) = 914345315861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_79
      · exact prime_sixtyFourBJ_1693
      · exact prime_sixtyFourBJ_20107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 914345315861) ^ 457172657930 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 914345315861) ^ 182869063172 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 914345315861) ^ 53785018580 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 914345315861) ^ 11573991340 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 914345315861) ^ 540074020 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 914345315861) ^ 45473980 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1581607550693 : Nat.Prime 1581607550693 := by
  apply lucas_primality 1581607550693 (2 : ZMod 1581607550693)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (19, 1), (94165727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (19, 1), (94165727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1581607550693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_94165727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1581607550693) ^ 790803775346 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581607550693) ^ 121662119284 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581607550693) ^ 93035738276 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581607550693) ^ 83242502668 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581607550693) ^ 16796 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1795958943791 : Nat.Prime 1795958943791 := by
  apply lucas_primality 1795958943791 (11 : ZMod 1795958943791)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (67, 1), (1231, 1), (197957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (67, 1), (1231, 1), (197957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1795958943791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_67
      · exact prime_sixtyFourBJ_1231
      · exact prime_sixtyFourBJ_197957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1795958943791) ^ 897979471895 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1795958943791) ^ 359191788758 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1795958943791) ^ 163268994890 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1795958943791) ^ 26805357370 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1795958943791) ^ 1458943090 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1795958943791) ^ 9072470 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1828690631723 : Nat.Prime 1828690631723 := by
  apply lucas_primality 1828690631723 (2 : ZMod 1828690631723)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (914345315861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (914345315861, 1)] : List FactorBlock).map factorBlockValue).prod) = 1828690631723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_914345315861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1828690631723) ^ 914345315861 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1828690631723) ^ 2 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2315872143199 : Nat.Prime 2315872143199 := by
  apply lucas_primality 2315872143199 (3 : ZMod 2315872143199)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (141073, 1), (912007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (141073, 1), (912007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2315872143199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_141073
      · exact prime_sixtyFourBJ_912007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2315872143199) ^ 1157936071599 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2315872143199) ^ 771957381066 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2315872143199) ^ 16416126 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2315872143199) ^ 2539314 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2878390061969 : Nat.Prime 2878390061969 := by
  apply lucas_primality 2878390061969 (3 : ZMod 2878390061969)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (47, 1), (163, 1), (1051, 1), (22343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (47, 1), (163, 1), (1051, 1), (22343, 1)] : List FactorBlock).map factorBlockValue).prod) = 2878390061969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_47
      · exact prime_sixtyFourBJ_163
      · exact prime_sixtyFourBJ_1051
      · exact prime_sixtyFourBJ_22343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2878390061969) ^ 1439195030984 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2878390061969) ^ 61242341744 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2878390061969) ^ 17658834736 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2878390061969) ^ 2738715568 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2878390061969) ^ 128827376 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3391537149019 : Nat.Prime 3391537149019 := by
  apply lucas_primality 3391537149019 (3 : ZMod 3391537149019)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (22807, 1), (8261443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (22807, 1), (8261443, 1)] : List FactorBlock).map factorBlockValue).prod) = 3391537149019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_22807
      · exact prime_sixtyFourBJ_8261443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3391537149019) ^ 1695768574509 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3391537149019) ^ 1130512383006 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3391537149019) ^ 148705974 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3391537149019) ^ 410526 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3394783301017 : Nat.Prime 3394783301017 := by
  apply lucas_primality 3394783301017 (5 : ZMod 3394783301017)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (151, 1), (4129, 1), (226871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (151, 1), (4129, 1), (226871, 1)] : List FactorBlock).map factorBlockValue).prod) = 3394783301017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_151
      · exact prime_sixtyFourBJ_4129
      · exact prime_sixtyFourBJ_226871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3394783301017) ^ 1697391650508 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3394783301017) ^ 1131594433672 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3394783301017) ^ 22482008616 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3394783301017) ^ 822180504 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3394783301017) ^ 14963496 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3591917887583 : Nat.Prime 3591917887583 := by
  apply lucas_primality 3591917887583 (5 : ZMod 3591917887583)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1795958943791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1795958943791, 1)] : List FactorBlock).map factorBlockValue).prod) = 3591917887583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_1795958943791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 3591917887583) ^ 1795958943791 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3591917887583) ^ 2 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3641529292469 : Nat.Prime 3641529292469 := by
  apply lucas_primality 3641529292469 (2 : ZMod 3641529292469)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53411, 1), (17044847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53411, 1), (17044847, 1)] : List FactorBlock).map factorBlockValue).prod) = 3641529292469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_53411
      · exact prime_sixtyFourBJ_17044847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3641529292469) ^ 1820764646234 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641529292469) ^ 68179388 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641529292469) ^ 213644 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3721590152573 : Nat.Prime 3721590152573 := by
  apply lucas_primality 3721590152573 (2 : ZMod 3721590152573)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (17554670531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (17554670531, 1)] : List FactorBlock).map factorBlockValue).prod) = 3721590152573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_53
      · exact prime_sixtyFourBJ_17554670531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3721590152573) ^ 1860795076286 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3721590152573) ^ 70218682124 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3721590152573) ^ 212 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3935266187689 : Nat.Prime 3935266187689 := by
  apply lucas_primality 3935266187689 (13 : ZMod 3935266187689)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (1656256813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (1656256813, 1)] : List FactorBlock).map factorBlockValue).prod) = 3935266187689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_1656256813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3935266187689) ^ 1967633093844 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3935266187689) ^ 1311755395896 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3935266187689) ^ 357751471608 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3935266187689) ^ 2376 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_4554874136069 : Nat.Prime 4554874136069 := by
  apply lucas_primality 4554874136069 (2 : ZMod 4554874136069)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (49509501479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (49509501479, 1)] : List FactorBlock).map factorBlockValue).prod) = 4554874136069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_49509501479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4554874136069) ^ 2277437068034 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4554874136069) ^ 198038005916 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4554874136069) ^ 92 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_5577011752699 : Nat.Prime 5577011752699 := by
  apply lucas_primality 5577011752699 (17 : ZMod 5577011752699)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (309833986261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (309833986261, 1)] : List FactorBlock).map factorBlockValue).prod) = 5577011752699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_309833986261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 5577011752699) ^ 2788505876349 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5577011752699) ^ 1859003917566 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 5577011752699) ^ 18 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_5610730450477 : Nat.Prime 5610730450477 := by
  apply lucas_primality 5610730450477 (5 : ZMod 5610730450477)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (74941, 1), (6239053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (74941, 1), (6239053, 1)] : List FactorBlock).map factorBlockValue).prod) = 5610730450477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_74941
      · exact prime_sixtyFourBJ_6239053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5610730450477) ^ 2805365225238 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5610730450477) ^ 1870243483492 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5610730450477) ^ 74868636 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5610730450477) ^ 899292 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_6725299936097 : Nat.Prime 6725299936097 := by
  apply lucas_primality 6725299936097 (5 : ZMod 6725299936097)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (6271, 1), (683957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (6271, 1), (683957, 1)] : List FactorBlock).map factorBlockValue).prod) = 6725299936097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_6271
      · exact prime_sixtyFourBJ_683957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6725299936097) ^ 3362649968048 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6725299936097) ^ 960757133728 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6725299936097) ^ 1072444576 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6725299936097) ^ 9832928 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_7443180305147 : Nat.Prime 7443180305147 := by
  apply lucas_primality 7443180305147 (2 : ZMod 7443180305147)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3721590152573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3721590152573, 1)] : List FactorBlock).map factorBlockValue).prod) = 7443180305147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3721590152573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7443180305147) ^ 3721590152573 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7443180305147) ^ 2 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_8516764235431 : Nat.Prime 8516764235431 := by
  apply lucas_primality 8516764235431 (7 : ZMod 8516764235431)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (47, 1), (183038131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (47, 1), (183038131, 1)] : List FactorBlock).map factorBlockValue).prod) = 8516764235431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_47
      · exact prime_sixtyFourBJ_183038131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8516764235431) ^ 4258382117715 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8516764235431) ^ 2838921411810 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8516764235431) ^ 1703352847086 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8516764235431) ^ 774251294130 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8516764235431) ^ 181207749690 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8516764235431) ^ 46530 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_8998919122471 : Nat.Prime 8998919122471 := by
  apply lucas_primality 8998919122471 (3 : ZMod 8998919122471)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2851, 1), (105213599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2851, 1), (105213599, 1)] : List FactorBlock).map factorBlockValue).prod) = 8998919122471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_2851
      · exact prime_sixtyFourBJ_105213599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8998919122471) ^ 4499459561235 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8998919122471) ^ 2999639707490 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8998919122471) ^ 1799783824494 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8998919122471) ^ 3156407970 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8998919122471) ^ 85530 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_13456570640549 : Nat.Prime 13456570640549 := by
  apply lucas_primality 13456570640549 (2 : ZMod 13456570640549)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (480591808591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (480591808591, 1)] : List FactorBlock).map factorBlockValue).prod) = 13456570640549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_480591808591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13456570640549) ^ 6728285320274 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13456570640549) ^ 1922367234364 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13456570640549) ^ 28 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_13770496402307 : Nat.Prime 13770496402307 := by
  apply lucas_primality 13770496402307 (2 : ZMod 13770496402307)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (937171, 1), (1049549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (937171, 1), (1049549, 1)] : List FactorBlock).map factorBlockValue).prod) = 13770496402307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_937171
      · exact prime_sixtyFourBJ_1049549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13770496402307) ^ 6885248201153 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13770496402307) ^ 1967213771758 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13770496402307) ^ 14693686 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13770496402307) ^ 13120394 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_14384694927139 : Nat.Prime 14384694927139 := by
  apply lucas_primality 14384694927139 (10 : ZMod 14384694927139)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (241, 1), (859, 1), (11580817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (241, 1), (859, 1), (11580817, 1)] : List FactorBlock).map factorBlockValue).prod) = 14384694927139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_241
      · exact prime_sixtyFourBJ_859
      · exact prime_sixtyFourBJ_11580817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 14384694927139) ^ 7192347463569 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 14384694927139) ^ 4794898309046 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 14384694927139) ^ 59687530818 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 14384694927139) ^ 16745861382 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 14384694927139) ^ 1242114 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_22332597053483 : Nat.Prime 22332597053483 := by
  apply lucas_primality 22332597053483 (2 : ZMod 22332597053483)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (73, 1), (2267, 1), (1569157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (73, 1), (2267, 1), (1569157, 1)] : List FactorBlock).map factorBlockValue).prod) = 22332597053483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_43
      · exact prime_sixtyFourBJ_73
      · exact prime_sixtyFourBJ_2267
      · exact prime_sixtyFourBJ_1569157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22332597053483) ^ 11166298526741 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22332597053483) ^ 519362722174 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22332597053483) ^ 305925987034 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22332597053483) ^ 9851167646 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 22332597053483) ^ 14232226 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_23158721431991 : Nat.Prime 23158721431991 := by
  apply lucas_primality 23158721431991 (17 : ZMod 23158721431991)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2315872143199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2315872143199, 1)] : List FactorBlock).map factorBlockValue).prod) = 23158721431991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_2315872143199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 23158721431991) ^ 11579360715995 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 23158721431991) ^ 4631744286398 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 23158721431991) ^ 10 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_24014392165877 : Nat.Prime 24014392165877 := by
  apply lucas_primality 24014392165877 (2 : ZMod 24014392165877)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (71593, 1), (520853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (71593, 1), (520853, 1)] : List FactorBlock).map factorBlockValue).prod) = 24014392165877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_71593
      · exact prime_sixtyFourBJ_520853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24014392165877) ^ 12007196082938 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24014392165877) ^ 3430627452268 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24014392165877) ^ 1044104007212 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24014392165877) ^ 335429332 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24014392165877) ^ 46105892 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_24894828203711 : Nat.Prime 24894828203711 := by
  apply lucas_primality 24894828203711 (7 : ZMod 24894828203711)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1129, 1), (2205033499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1129, 1), (2205033499, 1)] : List FactorBlock).map factorBlockValue).prod) = 24894828203711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_1129
      · exact prime_sixtyFourBJ_2205033499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 24894828203711) ^ 12447414101855 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 24894828203711) ^ 4978965640742 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 24894828203711) ^ 22050334990 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 24894828203711) ^ 11290 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_26913141281099 : Nat.Prime 26913141281099 := by
  apply lucas_primality 26913141281099 (2 : ZMod 26913141281099)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13456570640549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13456570640549, 1)] : List FactorBlock).map factorBlockValue).prod) = 26913141281099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13456570640549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 26913141281099) ^ 13456570640549 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26913141281099) ^ 2 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_28251849536513 : Nat.Prime 28251849536513 := by
  apply lucas_primality 28251849536513 (5 : ZMod 28251849536513)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (7, 2), (23627, 1), (23831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (7, 2), (23627, 1), (23831, 1)] : List FactorBlock).map factorBlockValue).prod) = 28251849536513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_23627
      · exact prime_sixtyFourBJ_23831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28251849536513) ^ 14125924768256 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 28251849536513) ^ 4035978505216 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 28251849536513) ^ 1195744256 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 28251849536513) ^ 1185508352 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_30226467755111 : Nat.Prime 30226467755111 := by
  apply lucas_primality 30226467755111 (11 : ZMod 30226467755111)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (274786070501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (274786070501, 1)] : List FactorBlock).map factorBlockValue).prod) = 30226467755111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_274786070501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 30226467755111) ^ 15113233877555 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 30226467755111) ^ 6045293551022 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 30226467755111) ^ 2747860705010 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 30226467755111) ^ 110 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_39109390090819 : Nat.Prime 39109390090819 := by
  apply lucas_primality 39109390090819 (3 : ZMod 39109390090819)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (28463893807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (28463893807, 1)] : List FactorBlock).map factorBlockValue).prod) = 39109390090819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_229
      · exact prime_sixtyFourBJ_28463893807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39109390090819) ^ 19554695045409 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 39109390090819) ^ 13036463363606 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 39109390090819) ^ 170783362842 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 39109390090819) ^ 1374 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_43107473975941 : Nat.Prime 43107473975941 := by
  apply lucas_primality 43107473975941 (10 : ZMod 43107473975941)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (11, 1), (29, 1), (83415523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (11, 1), (29, 1), (83415523, 1)] : List FactorBlock).map factorBlockValue).prod) = 43107473975941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_83415523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 43107473975941) ^ 21553736987970 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 43107473975941) ^ 14369157991980 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 43107473975941) ^ 8621494795188 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 43107473975941) ^ 3918861270540 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 43107473975941) ^ 1486464619860 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 43107473975941) ^ 516780 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_61466750512373 : Nat.Prime 61466750512373 := by
  apply lucas_primality 61466750512373 (2 : ZMod 61466750512373)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (47939, 1), (4057553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (47939, 1), (4057553, 1)] : List FactorBlock).map factorBlockValue).prod) = 61466750512373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_79
      · exact prime_sixtyFourBJ_47939
      · exact prime_sixtyFourBJ_4057553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61466750512373) ^ 30733375256186 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61466750512373) ^ 778060133068 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61466750512373) ^ 1282186748 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 61466750512373) ^ 15148724 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_73704937611727 : Nat.Prime 73704937611727 := by
  apply lucas_primality 73704937611727 (5 : ZMod 73704937611727)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (61, 1), (22375512329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (61, 1), (22375512329, 1)] : List FactorBlock).map factorBlockValue).prod) = 73704937611727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_61
      · exact prime_sixtyFourBJ_22375512329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 73704937611727) ^ 36852468805863 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 73704937611727) ^ 24568312537242 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 73704937611727) ^ 1208277665766 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 73704937611727) ^ 3294 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_100001854277041 : Nat.Prime 100001854277041 := by
  apply lucas_primality 100001854277041 (7 : ZMod 100001854277041)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (416674392821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (416674392821, 1)] : List FactorBlock).map factorBlockValue).prod) = 100001854277041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_416674392821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 100001854277041) ^ 50000927138520 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100001854277041) ^ 33333951425680 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100001854277041) ^ 20000370855408 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100001854277041) ^ 240 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_113365844294237 : Nat.Prime 113365844294237 := by
  apply lucas_primality 113365844294237 (2 : ZMod 113365844294237)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3785569, 1), (7486711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3785569, 1), (7486711, 1)] : List FactorBlock).map factorBlockValue).prod) = 113365844294237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3785569
      · exact prime_sixtyFourBJ_7486711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 113365844294237) ^ 56682922147118 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 113365844294237) ^ 29946844 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 113365844294237) ^ 15142276 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_173939948253587 : Nat.Prime 173939948253587 := by
  apply lucas_primality 173939948253587 (2 : ZMod 173939948253587)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21487, 1), (4047562439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21487, 1), (4047562439, 1)] : List FactorBlock).map factorBlockValue).prod) = 173939948253587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_21487
      · exact prime_sixtyFourBJ_4047562439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173939948253587) ^ 86969974126793 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 173939948253587) ^ 8095124878 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 173939948253587) ^ 42974 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_185088044451811 : Nat.Prime 185088044451811 := by
  apply lucas_primality 185088044451811 (3 : ZMod 185088044451811)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (131, 1), (47096194517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (131, 1), (47096194517, 1)] : List FactorBlock).map factorBlockValue).prod) = 185088044451811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_131
      · exact prime_sixtyFourBJ_47096194517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 185088044451811) ^ 92544022225905 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 185088044451811) ^ 61696014817270 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 185088044451811) ^ 37017608890362 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 185088044451811) ^ 1412885835510 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 185088044451811) ^ 3930 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_187043565821111 : Nat.Prime 187043565821111 := by
  apply lucas_primality 187043565821111 (31 : ZMod 187043565821111)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13931, 1), (1342642781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13931, 1), (1342642781, 1)] : List FactorBlock).map factorBlockValue).prod) = 187043565821111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_13931
      · exact prime_sixtyFourBJ_1342642781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 187043565821111) ^ 93521782910555 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (31 : ZMod 187043565821111) ^ 37408713164222 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (31 : ZMod 187043565821111) ^ 13426427810 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (31 : ZMod 187043565821111) ^ 139310 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_296854786162783 : Nat.Prime 296854786162783 := by
  apply lucas_primality 296854786162783 (3 : ZMod 296854786162783)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10369, 1), (14479, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10369, 1), (14479, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) = 296854786162783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_10369
      · exact prime_sixtyFourBJ_14479
      · exact prime_sixtyFourBJ_109849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 296854786162783) ^ 148427393081391 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 296854786162783) ^ 98951595387594 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 296854786162783) ^ 28629066078 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 296854786162783) ^ 20502437058 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 296854786162783) ^ 2702389518 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_309971832918133 : Nat.Prime 309971832918133 := by
  apply lucas_primality 309971832918133 (5 : ZMod 309971832918133)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (83, 1), (263, 1), (2383, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (83, 1), (263, 1), (2383, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) = 309971832918133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_83
      · exact prime_sixtyFourBJ_263
      · exact prime_sixtyFourBJ_2383
      · exact prime_sixtyFourBJ_6449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 309971832918133) ^ 154985916459066 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 309971832918133) ^ 103323944306044 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 309971832918133) ^ 44281690416876 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 309971832918133) ^ 28179257538012 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 309971832918133) ^ 3734600396604 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 309971832918133) ^ 1178600125164 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 309971832918133) ^ 130076304204 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 309971832918133) ^ 48065100468 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_325659698444609 : Nat.Prime 325659698444609 := by
  apply lucas_primality 325659698444609 (3 : ZMod 325659698444609)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 1), (29, 1), (93337, 1), (170899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 1), (29, 1), (93337, 1), (170899, 1)] : List FactorBlock).map factorBlockValue).prod) = 325659698444609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_93337
      · exact prime_sixtyFourBJ_170899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 325659698444609) ^ 162829849222304 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 325659698444609) ^ 29605427131328 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 325659698444609) ^ 11229644773952 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 325659698444609) ^ 3489073984 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 325659698444609) ^ 1905568192 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_368103527797769 : Nat.Prime 368103527797769 := by
  apply lucas_primality 368103527797769 (3 : ZMod 368103527797769)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (47, 1), (167, 1), (6553, 1), (18257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (47, 1), (167, 1), (6553, 1), (18257, 1)] : List FactorBlock).map factorBlockValue).prod) = 368103527797769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_47
      · exact prime_sixtyFourBJ_167
      · exact prime_sixtyFourBJ_6553
      · exact prime_sixtyFourBJ_18257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 368103527797769) ^ 184051763898884 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368103527797769) ^ 52586218256824 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368103527797769) ^ 7831989953144 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368103527797769) ^ 2204212741304 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368103527797769) ^ 56173283656 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368103527797769) ^ 20162322824 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_368395700330263 : Nat.Prime 368395700330263 := by
  apply lucas_primality 368395700330263 (3 : ZMod 368395700330263)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2777, 1), (3929, 1), (511579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2777, 1), (3929, 1), (511579, 1)] : List FactorBlock).map factorBlockValue).prod) = 368395700330263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_2777
      · exact prime_sixtyFourBJ_3929
      · exact prime_sixtyFourBJ_511579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 368395700330263) ^ 184197850165131 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368395700330263) ^ 122798566776754 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368395700330263) ^ 33490518211842 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368395700330263) ^ 132659596806 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368395700330263) ^ 93763222278 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 368395700330263) ^ 720114978 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_417400897009819 : Nat.Prime 417400897009819 := by
  apply lucas_primality 417400897009819 (2 : ZMod 417400897009819)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (410233, 1), (9975223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (410233, 1), (9975223, 1)] : List FactorBlock).map factorBlockValue).prod) = 417400897009819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_410233
      · exact prime_sixtyFourBJ_9975223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 417400897009819) ^ 208700448504909 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 417400897009819) ^ 139133632336606 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 417400897009819) ^ 24552993941754 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 417400897009819) ^ 1017472746 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 417400897009819) ^ 41843766 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_529256239084891 : Nat.Prime 529256239084891 := by
  apply lucas_primality 529256239084891 (3 : ZMod 529256239084891)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (17, 1), (37, 1), (571, 1), (5457773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (17, 1), (37, 1), (571, 1), (5457773, 1)] : List FactorBlock).map factorBlockValue).prod) = 529256239084891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_37
      · exact prime_sixtyFourBJ_571
      · exact prime_sixtyFourBJ_5457773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 529256239084891) ^ 264628119542445 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529256239084891) ^ 176418746361630 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529256239084891) ^ 105851247816978 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529256239084891) ^ 31132719946170 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529256239084891) ^ 14304222677970 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529256239084891) ^ 926893588590 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 529256239084891) ^ 96972930 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_720431764976311 : Nat.Prime 720431764976311 := by
  apply lucas_primality 720431764976311 (6 : ZMod 720431764976311)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (24014392165877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (24014392165877, 1)] : List FactorBlock).map factorBlockValue).prod) = 720431764976311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_24014392165877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 720431764976311) ^ 360215882488155 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 720431764976311) ^ 240143921658770 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 720431764976311) ^ 144086352995262 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 720431764976311) ^ 30 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_966842147993819 : Nat.Prime 966842147993819 := by
  apply lucas_primality 966842147993819 (2 : ZMod 966842147993819)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (571, 1), (18133, 1), (2029981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (571, 1), (18133, 1), (2029981, 1)] : List FactorBlock).map factorBlockValue).prod) = 966842147993819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_571
      · exact prime_sixtyFourBJ_18133
      · exact prime_sixtyFourBJ_2029981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 966842147993819) ^ 483421073996909 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 966842147993819) ^ 42036615130166 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 966842147993819) ^ 1693243691758 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 966842147993819) ^ 53319480946 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 966842147993819) ^ 476281378 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1768119162085819 : Nat.Prime 1768119162085819 := by
  apply lucas_primality 1768119162085819 (2 : ZMod 1768119162085819)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (276487, 1), (355274723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (276487, 1), (355274723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1768119162085819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_276487
      · exact prime_sixtyFourBJ_355274723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1768119162085819) ^ 884059581042909 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768119162085819) ^ 589373054028606 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768119162085819) ^ 6394945014 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768119162085819) ^ 4976766 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3861209077232581 : Nat.Prime 3861209077232581 := by
  apply lucas_primality 3861209077232581 (2 : ZMod 3861209077232581)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (457, 1), (46939084333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (457, 1), (46939084333, 1)] : List FactorBlock).map factorBlockValue).prod) = 3861209077232581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_457
      · exact prime_sixtyFourBJ_46939084333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3861209077232581) ^ 1930604538616290 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3861209077232581) ^ 1287069692410860 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3861209077232581) ^ 772241815446516 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3861209077232581) ^ 8449035179940 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3861209077232581) ^ 82260 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_4307902083181007 : Nat.Prime 4307902083181007 := by
  apply lucas_primality 4307902083181007 (5 : ZMod 4307902083181007)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (113365844294237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (113365844294237, 1)] : List FactorBlock).map factorBlockValue).prod) = 4307902083181007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_113365844294237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4307902083181007) ^ 2153951041590503 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4307902083181007) ^ 226731688588474 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4307902083181007) ^ 38 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_6279016535947723 : Nat.Prime 6279016535947723 := by
  apply lucas_primality 6279016535947723 (3 : ZMod 6279016535947723)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (47, 1), (71, 1), (6400119599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (47, 1), (71, 1), (6400119599, 1)] : List FactorBlock).map factorBlockValue).prod) = 6279016535947723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_47
      · exact prime_sixtyFourBJ_71
      · exact prime_sixtyFourBJ_6400119599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6279016535947723) ^ 3139508267973861 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6279016535947723) ^ 2093005511982574 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6279016535947723) ^ 897002362278246 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6279016535947723) ^ 133596096509526 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6279016535947723) ^ 88436852618982 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6279016535947723) ^ 981078 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_9124319693144713 : Nat.Prime 9124319693144713 := by
  apply lucas_primality 9124319693144713 (13 : ZMod 9124319693144713)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (179, 1), (303415791871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (179, 1), (303415791871, 1)] : List FactorBlock).map factorBlockValue).prod) = 9124319693144713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_179
      · exact prime_sixtyFourBJ_303415791871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9124319693144713) ^ 4562159846572356 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9124319693144713) ^ 3041439897714904 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9124319693144713) ^ 1303474241877816 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9124319693144713) ^ 50973853034328 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9124319693144713) ^ 30072 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_15014108939756023 : Nat.Prime 15014108939756023 := by
  apply lucas_primality 15014108939756023 (3 : ZMod 15014108939756023)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (359, 1), (1531, 1), (13922939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (359, 1), (1531, 1), (13922939, 1)] : List FactorBlock).map factorBlockValue).prod) = 15014108939756023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_109
      · exact prime_sixtyFourBJ_359
      · exact prime_sixtyFourBJ_1531
      · exact prime_sixtyFourBJ_13922939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15014108939756023) ^ 7507054469878011 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15014108939756023) ^ 5004702979918674 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15014108939756023) ^ 137744118713358 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15014108939756023) ^ 41822030472858 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15014108939756023) ^ 9806733468162 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15014108939756023) ^ 1078372098 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_16032610377286639 : Nat.Prime 16032610377286639 := by
  apply lucas_primality 16032610377286639 (3 : ZMod 16032610377286639)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (7443180305147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (7443180305147, 1)] : List FactorBlock).map factorBlockValue).prod) = 16032610377286639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_359
      · exact prime_sixtyFourBJ_7443180305147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16032610377286639) ^ 8016305188643319 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16032610377286639) ^ 5344203459095546 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16032610377286639) ^ 44659081830882 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16032610377286639) ^ 2154 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_16478136236832713 : Nat.Prime 16478136236832713 := by
  apply lucas_primality 16478136236832713 (3 : ZMod 16478136236832713)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (613, 1), (5009, 1), (51601609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (613, 1), (5009, 1), (51601609, 1)] : List FactorBlock).map factorBlockValue).prod) = 16478136236832713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_613
      · exact prime_sixtyFourBJ_5009
      · exact prime_sixtyFourBJ_51601609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16478136236832713) ^ 8239068118416356 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16478136236832713) ^ 1267548941294824 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16478136236832713) ^ 26881135786024 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16478136236832713) ^ 3289705776968 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16478136236832713) ^ 319333768 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_17924770698074783 : Nat.Prime 17924770698074783 := by
  apply lucas_primality 17924770698074783 (5 : ZMod 17924770698074783)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (6197, 1), (75337, 1), (834653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (6197, 1), (75337, 1), (834653, 1)] : List FactorBlock).map factorBlockValue).prod) = 17924770698074783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_6197
      · exact prime_sixtyFourBJ_75337
      · exact prime_sixtyFourBJ_834653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17924770698074783) ^ 8962385349037391 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17924770698074783) ^ 779337856438034 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17924770698074783) ^ 2892491640806 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17924770698074783) ^ 237927853486 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17924770698074783) ^ 21475715894 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_21611336513322341 : Nat.Prime 21611336513322341 := by
  apply lucas_primality 21611336513322341 (3 : ZMod 21611336513322341)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (157, 1), (146438111623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (157, 1), (146438111623, 1)] : List FactorBlock).map factorBlockValue).prod) = 21611336513322341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_47
      · exact prime_sixtyFourBJ_157
      · exact prime_sixtyFourBJ_146438111623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21611336513322341) ^ 10805668256661170 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 21611336513322341) ^ 4322267302664468 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 21611336513322341) ^ 459815670496220 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 21611336513322341) ^ 137651824925620 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 21611336513322341) ^ 147580 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_51176294158924423 : Nat.Prime 51176294158924423 := by
  apply lucas_primality 51176294158924423 (3 : ZMod 51176294158924423)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (2861, 1), (119771, 1), (921901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (2861, 1), (119771, 1), (921901, 1)] : List FactorBlock).map factorBlockValue).prod) = 51176294158924423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_2861
      · exact prime_sixtyFourBJ_119771
      · exact prime_sixtyFourBJ_921901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51176294158924423) ^ 25588147079462211 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51176294158924423) ^ 17058764719641474 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51176294158924423) ^ 17887554756702 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51176294158924423) ^ 427284519282 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51176294158924423) ^ 55511702622 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_60056435759024093 : Nat.Prime 60056435759024093 := by
  apply lucas_primality 60056435759024093 (2 : ZMod 60056435759024093)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15014108939756023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15014108939756023, 1)] : List FactorBlock).map factorBlockValue).prod) = 60056435759024093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_15014108939756023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 60056435759024093) ^ 30028217879512046 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60056435759024093) ^ 4 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_65790048948804073 : Nat.Prime 65790048948804073 := by
  apply lucas_primality 65790048948804073 (5 : ZMod 65790048948804073)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (17, 1), (29, 1), (211, 1), (13523, 1), (216523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (17, 1), (29, 1), (211, 1), (13523, 1), (216523, 1)] : List FactorBlock).map factorBlockValue).prod) = 65790048948804073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_211
      · exact prime_sixtyFourBJ_13523
      · exact prime_sixtyFourBJ_216523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 65790048948804073) ^ 32895024474402036 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 65790048948804073) ^ 21930016316268024 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 65790048948804073) ^ 3870002879341416 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 65790048948804073) ^ 2268622377544968 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 65790048948804073) ^ 311801179852152 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 65790048948804073) ^ 4865048358264 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 65790048948804073) ^ 303847854264 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_133964612068318751 : Nat.Prime 133964612068318751 := by
  apply lucas_primality 133964612068318751 (11 : ZMod 133964612068318751)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 5), (73, 1), (466171, 1), (629857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 5), (73, 1), (466171, 1), (629857, 1)] : List FactorBlock).map factorBlockValue).prod) = 133964612068318751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_73
      · exact prime_sixtyFourBJ_466171
      · exact prime_sixtyFourBJ_629857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 133964612068318751) ^ 66982306034159375 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 133964612068318751) ^ 26792922413663750 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 133964612068318751) ^ 1835131672168750 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 133964612068318751) ^ 287372256250 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 133964612068318751) ^ 212690518750 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_163700279160878267 : Nat.Prime 163700279160878267 := by
  apply lucas_primality 163700279160878267 (2 : ZMod 163700279160878267)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (4307902083181007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (4307902083181007, 1)] : List FactorBlock).map factorBlockValue).prod) = 163700279160878267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_4307902083181007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 163700279160878267) ^ 81850139580439133 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 163700279160878267) ^ 8615804166362014 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 163700279160878267) ^ 38 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_200436557578066819 : Nat.Prime 200436557578066819 := by
  apply lucas_primality 200436557578066819 (2 : ZMod 200436557578066819)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (12713, 1), (30203577413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (12713, 1), (30203577413, 1)] : List FactorBlock).map factorBlockValue).prod) = 200436557578066819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_12713
      · exact prime_sixtyFourBJ_30203577413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200436557578066819) ^ 100218278789033409 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 200436557578066819) ^ 66812185859355606 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 200436557578066819) ^ 6911605433726442 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 200436557578066819) ^ 15766267409586 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 200436557578066819) ^ 6636186 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_215484183812838839 : Nat.Prime 215484183812838839 := by
  apply lucas_primality 215484183812838839 (13 : ZMod 215484183812838839)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (474757, 1), (226941555167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (474757, 1), (226941555167, 1)] : List FactorBlock).map factorBlockValue).prod) = 215484183812838839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_474757
      · exact prime_sixtyFourBJ_226941555167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 215484183812838839) ^ 107742091906419419 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 215484183812838839) ^ 453883110334 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (13 : ZMod 215484183812838839) ^ 949514 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_328475508953209669 : Nat.Prime 328475508953209669 := by
  apply lucas_primality 328475508953209669 (2 : ZMod 328475508953209669)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (9124319693144713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (9124319693144713, 1)] : List FactorBlock).map factorBlockValue).prod) = 328475508953209669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_9124319693144713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 328475508953209669) ^ 164237754476604834 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 328475508953209669) ^ 109491836317736556 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 328475508953209669) ^ 36 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_426464659968860521 : Nat.Prime 426464659968860521 := by
  apply lucas_primality 426464659968860521 (11 : ZMod 426464659968860521)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (107, 1), (1581607550693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (107, 1), (1581607550693, 1)] : List FactorBlock).map factorBlockValue).prod) = 426464659968860521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_107
      · exact prime_sixtyFourBJ_1581607550693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 426464659968860521) ^ 213232329984430260 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 426464659968860521) ^ 142154886656286840 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 426464659968860521) ^ 85292931993772104 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 426464659968860521) ^ 60923522852694360 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 426464659968860521) ^ 3985651027746360 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 426464659968860521) ^ 269640 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_467293162200793387 : Nat.Prime 467293162200793387 := by
  apply lucas_primality 467293162200793387 (2 : ZMod 467293162200793387)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (4444789, 1), (922217641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (4444789, 1), (922217641, 1)] : List FactorBlock).map factorBlockValue).prod) = 467293162200793387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_4444789
      · exact prime_sixtyFourBJ_922217641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 467293162200793387) ^ 233646581100396693 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 467293162200793387) ^ 155764387400264462 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 467293162200793387) ^ 24594376957936494 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 467293162200793387) ^ 105132811074 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 467293162200793387) ^ 506705946 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_556614742937437087 : Nat.Prime 556614742937437087 := by
  apply lucas_primality 556614742937437087 (5 : ZMod 556614742937437087)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (71, 1), (12601, 1), (2116138139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (71, 1), (12601, 1), (2116138139, 1)] : List FactorBlock).map factorBlockValue).prod) = 556614742937437087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_71
      · exact prime_sixtyFourBJ_12601
      · exact prime_sixtyFourBJ_2116138139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 556614742937437087) ^ 278307371468718543 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 556614742937437087) ^ 185538247645812362 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 556614742937437087) ^ 79516391848205298 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 556614742937437087) ^ 7839644266724466 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 556614742937437087) ^ 44172267513486 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 556614742937437087) ^ 263033274 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_602785587450981409 : Nat.Prime 602785587450981409 := by
  apply lucas_primality 602785587450981409 (7 : ZMod 602785587450981409)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (6279016535947723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (6279016535947723, 1)] : List FactorBlock).map factorBlockValue).prod) = 602785587450981409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_6279016535947723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 602785587450981409) ^ 301392793725490704 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 602785587450981409) ^ 200928529150327136 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 602785587450981409) ^ 96 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_930781685472841061 : Nat.Prime 930781685472841061 := by
  apply lucas_primality 930781685472841061 (2 : ZMod 930781685472841061)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13709, 1), (3394783301017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13709, 1), (3394783301017, 1)] : List FactorBlock).map factorBlockValue).prod) = 930781685472841061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_13709
      · exact prime_sixtyFourBJ_3394783301017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 930781685472841061) ^ 465390842736420530 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 930781685472841061) ^ 186156337094568212 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 930781685472841061) ^ 67895666020340 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 930781685472841061) ^ 274180 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_954597771786408599 : Nat.Prime 954597771786408599 := by
  apply lucas_primality 954597771786408599 (11 : ZMod 954597771786408599)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131071, 1), (3641529292469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131071, 1), (3641529292469, 1)] : List FactorBlock).map factorBlockValue).prod) = 954597771786408599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_131071
      · exact prime_sixtyFourBJ_3641529292469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 954597771786408599) ^ 477298885893204299 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 954597771786408599) ^ 7283058584938 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 954597771786408599) ^ 262142 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1111079451051387791 : Nat.Prime 1111079451051387791 := by
  apply lucas_primality 1111079451051387791 (7 : ZMod 1111079451051387791)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1009, 1), (19429, 1), (809665177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1009, 1), (19429, 1), (809665177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1111079451051387791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_1009
      · exact prime_sixtyFourBJ_19429
      · exact prime_sixtyFourBJ_809665177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1111079451051387791) ^ 555539725525693895 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111079451051387791) ^ 222215890210277558 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111079451051387791) ^ 158725635864483970 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111079451051387791) ^ 1101168930675310 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111079451051387791) ^ 57186651451510 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1111079451051387791) ^ 1372270270 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1141612614338177909 : Nat.Prime 1141612614338177909 := by
  apply lucas_primality 1141612614338177909 (2 : ZMod 1141612614338177909)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (167, 1), (403063, 1), (41980537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (167, 1), (403063, 1), (41980537, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141612614338177909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_101
      · exact prime_sixtyFourBJ_167
      · exact prime_sixtyFourBJ_403063
      · exact prime_sixtyFourBJ_41980537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1141612614338177909) ^ 570806307169088954 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1141612614338177909) ^ 11303095191467108 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1141612614338177909) ^ 6836003678671724 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1141612614338177909) ^ 2832342870316 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1141612614338177909) ^ 27193854484 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1444816735378486817 : Nat.Prime 1444816735378486817 := by
  apply lucas_primality 1444816735378486817 (3 : ZMod 1444816735378486817)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (479, 1), (10601, 1), (41549, 1), (214003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (479, 1), (10601, 1), (41549, 1), (214003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1444816735378486817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_479
      · exact prime_sixtyFourBJ_10601
      · exact prime_sixtyFourBJ_41549
      · exact prime_sixtyFourBJ_214003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1444816735378486817) ^ 722408367689243408 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1444816735378486817) ^ 3016318863003104 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1444816735378486817) ^ 136290607997216 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1444816735378486817) ^ 34773802868384 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1444816735378486817) ^ 6751385426272 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1645080631097624647 : Nat.Prime 1645080631097624647 := by
  apply lucas_primality 1645080631097624647 (3 : ZMod 1645080631097624647)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (20919757, 1), (122488559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (20919757, 1), (122488559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1645080631097624647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_107
      · exact prime_sixtyFourBJ_20919757
      · exact prime_sixtyFourBJ_122488559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1645080631097624647) ^ 822540315548812323 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1645080631097624647) ^ 548360210365874882 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1645080631097624647) ^ 15374585337360978 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1645080631097624647) ^ 78637654878 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1645080631097624647) ^ 13430483994 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2299910841680460713 : Nat.Prime 2299910841680460713 := by
  apply lucas_primality 2299910841680460713 (3 : ZMod 2299910841680460713)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (71, 1), (368103527797769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (71, 1), (368103527797769, 1)] : List FactorBlock).map factorBlockValue).prod) = 2299910841680460713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_71
      · exact prime_sixtyFourBJ_368103527797769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2299910841680460713) ^ 1149955420840230356 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2299910841680460713) ^ 209082803789132792 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2299910841680460713) ^ 32393110446203672 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2299910841680460713) ^ 6248 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2418472980383135167 : Nat.Prime 2418472980383135167 := by
  apply lucas_primality 2418472980383135167 (3 : ZMod 2418472980383135167)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (157, 1), (1699, 1), (29629667777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (157, 1), (1699, 1), (29629667777, 1)] : List FactorBlock).map factorBlockValue).prod) = 2418472980383135167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_157
      · exact prime_sixtyFourBJ_1699
      · exact prime_sixtyFourBJ_29629667777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2418472980383135167) ^ 1209236490191567583 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2418472980383135167) ^ 806157660127711722 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2418472980383135167) ^ 142263116493125598 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2418472980383135167) ^ 15404286499255638 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2418472980383135167) ^ 1423468499342634 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2418472980383135167) ^ 81623358 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3972479078902837423 : Nat.Prime 3972479078902837423 := by
  apply lucas_primality 3972479078902837423 (5 : ZMod 3972479078902837423)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29, 1), (31, 1), (179, 1), (251, 1), (461, 1), (1545949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29, 1), (31, 1), (179, 1), (251, 1), (461, 1), (1545949, 1)] : List FactorBlock).map factorBlockValue).prod) = 3972479078902837423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_31
      · exact prime_sixtyFourBJ_179
      · exact prime_sixtyFourBJ_251
      · exact prime_sixtyFourBJ_461
      · exact prime_sixtyFourBJ_1545949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3972479078902837423) ^ 1986239539451418711 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 1324159692967612474 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 172716481691427714 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 136982037203546118 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 128144486416220562 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 22192620552529818 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 15826609876106922 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 8617091277446502 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3972479078902837423) ^ 2569605516678 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_4346280376733129279 : Nat.Prime 4346280376733129279 := by
  apply lucas_primality 4346280376733129279 (7 : ZMod 4346280376733129279)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (22159, 1), (115241267371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (22159, 1), (115241267371, 1)] : List FactorBlock).map factorBlockValue).prod) = 4346280376733129279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_37
      · exact prime_sixtyFourBJ_22159
      · exact prime_sixtyFourBJ_115241267371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4346280376733129279) ^ 2173140188366564639 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4346280376733129279) ^ 188968712031875186 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4346280376733129279) ^ 117467037209003494 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4346280376733129279) ^ 196140637065442 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4346280376733129279) ^ 37714618 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_4921896784205167883 : Nat.Prime 4921896784205167883 := by
  apply lucas_primality 4921896784205167883 (2 : ZMod 4921896784205167883)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (409, 1), (1321, 1), (4554874136069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (409, 1), (1321, 1), (4554874136069, 1)] : List FactorBlock).map factorBlockValue).prod) = 4921896784205167883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_409
      · exact prime_sixtyFourBJ_1321
      · exact prime_sixtyFourBJ_4554874136069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4921896784205167883) ^ 2460948392102583941 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4921896784205167883) ^ 12033977467494298 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4921896784205167883) ^ 3725887043304442 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4921896784205167883) ^ 1080578 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_5066998345753577393 : Nat.Prime 5066998345753577393 := by
  apply lucas_primality 5066998345753577393 (3 : ZMod 5066998345753577393)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (229, 1), (10067, 1), (3194675663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (229, 1), (10067, 1), (3194675663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5066998345753577393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_43
      · exact prime_sixtyFourBJ_229
      · exact prime_sixtyFourBJ_10067
      · exact prime_sixtyFourBJ_3194675663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5066998345753577393) ^ 2533499172876788696 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5066998345753577393) ^ 117837170831478544 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5066998345753577393) ^ 22126630330801648 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5066998345753577393) ^ 503327540056976 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5066998345753577393) ^ 1586075984 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_8006997915344690837 : Nat.Prime 8006997915344690837 := by
  apply lucas_primality 8006997915344690837 (3 : ZMod 8006997915344690837)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (10607227, 1), (1585845593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (10607227, 1), (1585845593, 1)] : List FactorBlock).map factorBlockValue).prod) = 8006997915344690837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_10607227
      · exact prime_sixtyFourBJ_1585845593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8006997915344690837) ^ 4003498957672345418 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8006997915344690837) ^ 1143856845049241548 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8006997915344690837) ^ 470999877373217108 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8006997915344690837) ^ 754862502268 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8006997915344690837) ^ 5049040052 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_8888635608411102329 : Nat.Prime 8888635608411102329 := by
  apply lucas_primality 8888635608411102329 (3 : ZMod 8888635608411102329)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1111079451051387791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1111079451051387791, 1)] : List FactorBlock).map factorBlockValue).prod) = 8888635608411102329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_1111079451051387791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 8888635608411102329) ^ 4444317804205551164 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8888635608411102329) ^ 8 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_11452754092568352689 : Nat.Prime 11452754092568352689 := by
  apply lucas_primality 11452754092568352689 (3 : ZMod 11452754092568352689)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1289, 1), (3463729, 1), (160322003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1289, 1), (3463729, 1), (160322003, 1)] : List FactorBlock).map factorBlockValue).prod) = 11452754092568352689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_1289
      · exact prime_sixtyFourBJ_3463729
      · exact prime_sixtyFourBJ_160322003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11452754092568352689) ^ 5726377046284176344 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11452754092568352689) ^ 8884991538066992 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11452754092568352689) ^ 3306480989872 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11452754092568352689) ^ 71435946896 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_30138032428908424057 : Nat.Prime 30138032428908424057 := by
  apply lucas_primality 30138032428908424057 (10 : ZMod 30138032428908424057)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (15823, 1), (521173, 1), (50758837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (15823, 1), (521173, 1), (50758837, 1)] : List FactorBlock).map factorBlockValue).prod) = 30138032428908424057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_15823
      · exact prime_sixtyFourBJ_521173
      · exact prime_sixtyFourBJ_50758837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 30138032428908424057) ^ 15069016214454212028 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 30138032428908424057) ^ 10046010809636141352 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 30138032428908424057) ^ 1904697745617672 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 30138032428908424057) ^ 57827309605272 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 30138032428908424057) ^ 593749467288 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_30622943819165669219 : Nat.Prime 30622943819165669219 := by
  apply lucas_primality 30622943819165669219 (2 : ZMod 30622943819165669219)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (7699, 1), (8998919122471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (7699, 1), (8998919122471, 1)] : List FactorBlock).map factorBlockValue).prod) = 30622943819165669219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_7699
      · exact prime_sixtyFourBJ_8998919122471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30622943819165669219) ^ 15311471909582834609 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622943819165669219) ^ 2355611063012743786 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622943819165669219) ^ 1801349636421509954 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622943819165669219) ^ 3977522252132182 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622943819165669219) ^ 3402958 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_31849181807568314179 : Nat.Prime 31849181807568314179 := by
  apply lucas_primality 31849181807568314179 (2 : ZMod 31849181807568314179)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (33547, 1), (14384694927139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (33547, 1), (14384694927139, 1)] : List FactorBlock).map factorBlockValue).prod) = 31849181807568314179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_33547
      · exact prime_sixtyFourBJ_14384694927139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31849181807568314179) ^ 15924590903784157089 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31849181807568314179) ^ 10616393935856104726 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31849181807568314179) ^ 2895380164324392198 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31849181807568314179) ^ 949389865191174 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 31849181807568314179) ^ 2214102 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_51647226895448155067 : Nat.Prime 51647226895448155067 := by
  apply lucas_primality 51647226895448155067 (2 : ZMod 51647226895448155067)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (2803, 1), (342989, 1), (1413709321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (2803, 1), (342989, 1), (1413709321, 1)] : List FactorBlock).map factorBlockValue).prod) = 51647226895448155067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_2803
      · exact prime_sixtyFourBJ_342989
      · exact prime_sixtyFourBJ_1413709321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51647226895448155067) ^ 25823613447724077533 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51647226895448155067) ^ 2718275099760429214 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51647226895448155067) ^ 18425696359417822 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51647226895448155067) ^ 150579834616994 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 51647226895448155067) ^ 36533130346 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_53981791190061936301 : Nat.Prime 53981791190061936301 := by
  apply lucas_primality 53981791190061936301 (2 : ZMod 53981791190061936301)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (11, 1), (347, 1), (1013, 1), (47623, 1), (325729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (11, 1), (347, 1), (1013, 1), (47623, 1), (325729, 1)] : List FactorBlock).map factorBlockValue).prod) = 53981791190061936301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_347
      · exact prime_sixtyFourBJ_1013
      · exact prime_sixtyFourBJ_47623
      · exact prime_sixtyFourBJ_325729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53981791190061936301) ^ 26990895595030968150 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53981791190061936301) ^ 17993930396687312100 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53981791190061936301) ^ 10796358238012387260 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53981791190061936301) ^ 4907435562732903300 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53981791190061936301) ^ 155567121585192900 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53981791190061936301) ^ 53289033751295100 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53981791190061936301) ^ 1133523532538100 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 53981791190061936301) ^ 165726082694700 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_54429413852227139989 : Nat.Prime 54429413852227139989 := by
  apply lucas_primality 54429413852227139989 (2 : ZMod 54429413852227139989)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (73, 1), (34649, 1), (94381145773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (73, 1), (34649, 1), (94381145773, 1)] : List FactorBlock).map factorBlockValue).prod) = 54429413852227139989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_73
      · exact prime_sixtyFourBJ_34649
      · exact prime_sixtyFourBJ_94381145773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54429413852227139989) ^ 27214706926113569994 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54429413852227139989) ^ 18143137950742379996 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54429413852227139989) ^ 2864705992222481052 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54429413852227139989) ^ 745608408934618356 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54429413852227139989) ^ 1570879790245812 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54429413852227139989) ^ 576697956 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_58301531992791279037 : Nat.Prime 58301531992791279037 := by
  apply lucas_primality 58301531992791279037 (6 : ZMod 58301531992791279037)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (41, 1), (101, 1), (392143, 1), (76715729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (41, 1), (101, 1), (392143, 1), (76715729, 1)] : List FactorBlock).map factorBlockValue).prod) = 58301531992791279037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_41
      · exact prime_sixtyFourBJ_101
      · exact prime_sixtyFourBJ_392143
      · exact prime_sixtyFourBJ_76715729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 58301531992791279037) ^ 29150765996395639518 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58301531992791279037) ^ 19433843997597093012 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58301531992791279037) ^ 4484733230214713772 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58301531992791279037) ^ 1421988585190031196 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58301531992791279037) ^ 577242891017735436 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58301531992791279037) ^ 148674162213252 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58301531992791279037) ^ 759968428284 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_63630908011947870091 : Nat.Prime 63630908011947870091 := by
  apply lucas_primality 63630908011947870091 (2 : ZMod 63630908011947870091)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (30871, 1), (103549, 1), (1662943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (30871, 1), (103549, 1), (1662943, 1)] : List FactorBlock).map factorBlockValue).prod) = 63630908011947870091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_30871
      · exact prime_sixtyFourBJ_103549
      · exact prime_sixtyFourBJ_1662943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63630908011947870091) ^ 31815454005973935045 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63630908011947870091) ^ 21210302670649290030 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63630908011947870091) ^ 12726181602389574018 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63630908011947870091) ^ 9090129715992552870 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63630908011947870091) ^ 3348995158523572110 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63630908011947870091) ^ 2061187133942790 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63630908011947870091) ^ 614500458835410 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 63630908011947870091) ^ 38264034312630 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_75357486244512801877 : Nat.Prime 75357486244512801877 := by
  apply lucas_primality 75357486244512801877 (2 : ZMod 75357486244512801877)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (119813, 1), (2589607, 1), (20239853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (119813, 1), (2589607, 1), (20239853, 1)] : List FactorBlock).map factorBlockValue).prod) = 75357486244512801877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_119813
      · exact prime_sixtyFourBJ_2589607
      · exact prime_sixtyFourBJ_20239853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75357486244512801877) ^ 37678743122256400938 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75357486244512801877) ^ 25119162081504267292 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75357486244512801877) ^ 628959180093252 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75357486244512801877) ^ 29099970089868 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 75357486244512801877) ^ 3723223001892 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_92485248636985510721 : Nat.Prime 92485248636985510721 := by
  apply lucas_primality 92485248636985510721 (3 : ZMod 92485248636985510721)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (191, 1), (997, 1), (172321, 1), (8807563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (191, 1), (997, 1), (172321, 1), (8807563, 1)] : List FactorBlock).map factorBlockValue).prod) = 92485248636985510721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_191
      · exact prime_sixtyFourBJ_997
      · exact prime_sixtyFourBJ_172321
      · exact prime_sixtyFourBJ_8807563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 92485248636985510721) ^ 46242624318492755360 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 92485248636985510721) ^ 18497049727397102144 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 92485248636985510721) ^ 484215961450185920 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 92485248636985510721) ^ 92763539254749760 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 92485248636985510721) ^ 536703295808320 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 92485248636985510721) ^ 10500662741440 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_115437705156613391579 : Nat.Prime 115437705156613391579 := by
  apply lucas_primality 115437705156613391579 (2 : ZMod 115437705156613391579)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 1), (1021, 1), (73704937611727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 1), (1021, 1), (73704937611727, 1)] : List FactorBlock).map factorBlockValue).prod) = 115437705156613391579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_59
      · exact prime_sixtyFourBJ_1021
      · exact prime_sixtyFourBJ_73704937611727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 115437705156613391579) ^ 57718852578306695789 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 115437705156613391579) ^ 8879823473585645506 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 115437705156613391579) ^ 1956571273840904942 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 115437705156613391579) ^ 113063374296389218 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 115437705156613391579) ^ 1566214 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_152719657757883376141 : Nat.Prime 152719657757883376141 := by
  apply lucas_primality 152719657757883376141 (2 : ZMod 152719657757883376141)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (133964612068318751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (133964612068318751, 1)] : List FactorBlock).map factorBlockValue).prod) = 152719657757883376141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_133964612068318751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 152719657757883376141) ^ 76359828878941688070 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 152719657757883376141) ^ 50906552585961125380 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 152719657757883376141) ^ 30543931551576675228 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 152719657757883376141) ^ 8037876724099125060 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 152719657757883376141) ^ 1140 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_166000685924635783597 : Nat.Prime 166000685924635783597 := by
  apply lucas_primality 166000685924635783597 (2 : ZMod 166000685924635783597)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (110337977, 1), (2199524297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (110337977, 1), (2199524297, 1)] : List FactorBlock).map factorBlockValue).prod) = 166000685924635783597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_110337977
      · exact prime_sixtyFourBJ_2199524297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 166000685924635783597) ^ 83000342962317891798 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 166000685924635783597) ^ 55333561974878594532 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 166000685924635783597) ^ 8736878206559778084 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 166000685924635783597) ^ 1504474619148 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 166000685924635783597) ^ 75471176268 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_199283991101396887031 : Nat.Prime 199283991101396887031 := by
  apply lucas_primality 199283991101396887031 (11 : ZMod 199283991101396887031)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (239, 1), (269, 1), (309971832918133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (239, 1), (269, 1), (309971832918133, 1)] : List FactorBlock).map factorBlockValue).prod) = 199283991101396887031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_239
      · exact prime_sixtyFourBJ_269
      · exact prime_sixtyFourBJ_309971832918133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 199283991101396887031) ^ 99641995550698443515 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 199283991101396887031) ^ 39856798220279377406 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 199283991101396887031) ^ 833824230549777770 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 199283991101396887031) ^ 740832680674337870 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 199283991101396887031) ^ 642910 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_268702662251865000889 : Nat.Prime 268702662251865000889 := by
  apply lucas_primality 268702662251865000889 (17 : ZMod 268702662251865000889)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (8941, 1), (417400897009819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (8941, 1), (417400897009819, 1)] : List FactorBlock).map factorBlockValue).prod) = 268702662251865000889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_8941
      · exact prime_sixtyFourBJ_417400897009819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 268702662251865000889) ^ 134351331125932500444 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 268702662251865000889) ^ 89567554083955000296 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 268702662251865000889) ^ 30052864584706968 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 268702662251865000889) ^ 643752 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_566701361369885309179 : Nat.Prime 566701361369885309179 := by
  apply lucas_primality 566701361369885309179 (3 : ZMod 566701361369885309179)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (9267619, 1), (783955627529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (9267619, 1), (783955627529, 1)] : List FactorBlock).map factorBlockValue).prod) = 566701361369885309179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_9267619
      · exact prime_sixtyFourBJ_783955627529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 566701361369885309179) ^ 283350680684942654589 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 566701361369885309179) ^ 188900453789961769726 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 566701361369885309179) ^ 43592412413068100706 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 566701361369885309179) ^ 61148538947262 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 566701361369885309179) ^ 722874282 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_985089480472584496453 : Nat.Prime 985089480472584496453 := by
  apply lucas_primality 985089480472584496453 (5 : ZMod 985089480472584496453)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5961353, 1), (13770496402307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5961353, 1), (13770496402307, 1)] : List FactorBlock).map factorBlockValue).prod) = 985089480472584496453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5961353
      · exact prime_sixtyFourBJ_13770496402307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 985089480472584496453) ^ 492544740236292248226 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 985089480472584496453) ^ 328363160157528165484 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 985089480472584496453) ^ 165245956827684 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 985089480472584496453) ^ 71536236 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1029336551332402431551 : Nat.Prime 1029336551332402431551 := by
  apply lucas_primality 1029336551332402431551 (17 : ZMod 1029336551332402431551)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2417201, 1), (8516764235431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2417201, 1), (8516764235431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1029336551332402431551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_2417201
      · exact prime_sixtyFourBJ_8516764235431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1029336551332402431551) ^ 514668275666201215775 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 1029336551332402431551) ^ 205867310266480486310 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 1029336551332402431551) ^ 425838211771550 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 1029336551332402431551) ^ 120860050 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1649441570561006312423 : Nat.Prime 1649441570561006312423 := by
  apply lucas_primality 1649441570561006312423 (5 : ZMod 1649441570561006312423)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (8006997915344690837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (8006997915344690837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1649441570561006312423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_103
      · exact prime_sixtyFourBJ_8006997915344690837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1649441570561006312423) ^ 824720785280503156211 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1649441570561006312423) ^ 16013995830689381674 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1649441570561006312423) ^ 206 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_1905975531914486003689 : Nat.Prime 1905975531914486003689 := by
  apply lucas_primality 1905975531914486003689 (17 : ZMod 1905975531914486003689)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2950813, 1), (26913141281099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2950813, 1), (26913141281099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1905975531914486003689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_2950813
      · exact prime_sixtyFourBJ_26913141281099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1905975531914486003689) ^ 952987765957243001844 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 1905975531914486003689) ^ 635325177304828667896 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 1905975531914486003689) ^ 645915390746376 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 1905975531914486003689) ^ 70819512 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2031977858852188094503 : Nat.Prime 2031977858852188094503 := by
  apply lucas_primality 2031977858852188094503 (5 : ZMod 2031977858852188094503)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3541, 1), (14221, 1), (6725299936097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3541, 1), (14221, 1), (6725299936097, 1)] : List FactorBlock).map factorBlockValue).prod) = 2031977858852188094503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_3541
      · exact prime_sixtyFourBJ_14221
      · exact prime_sixtyFourBJ_6725299936097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2031977858852188094503) ^ 1015988929426094047251 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2031977858852188094503) ^ 677325952950729364834 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2031977858852188094503) ^ 573842942347412622 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2031977858852188094503) ^ 142885722442316862 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2031977858852188094503) ^ 302139366 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2058673102664804863103 : Nat.Prime 2058673102664804863103 := by
  apply lucas_primality 2058673102664804863103 (5 : ZMod 2058673102664804863103)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1029336551332402431551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1029336551332402431551, 1)] : List FactorBlock).map factorBlockValue).prod) = 2058673102664804863103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_1029336551332402431551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2058673102664804863103) ^ 1029336551332402431551 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2058673102664804863103) ^ 2 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2512732868223835218323 : Nat.Prime 2512732868223835218323 := by
  apply lucas_primality 2512732868223835218323 (2 : ZMod 2512732868223835218323)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (84761, 1), (39109390090819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (84761, 1), (39109390090819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2512732868223835218323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_379
      · exact prime_sixtyFourBJ_84761
      · exact prime_sixtyFourBJ_39109390090819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2512732868223835218323) ^ 1256366434111917609161 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2512732868223835218323) ^ 6629902026975818518 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2512732868223835218323) ^ 29644917688840802 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2512732868223835218323) ^ 64248838 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_4777377271135247126851 : Nat.Prime 4777377271135247126851 := by
  apply lucas_primality 4777377271135247126851 (2 : ZMod 4777377271135247126851)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31849181807568314179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31849181807568314179, 1)] : List FactorBlock).map factorBlockValue).prod) = 4777377271135247126851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_31849181807568314179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4777377271135247126851) ^ 2388688635567623563425 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4777377271135247126851) ^ 1592459090378415708950 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4777377271135247126851) ^ 955475454227049425370 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4777377271135247126851) ^ 150 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_13807987799306841524603 : Nat.Prime 13807987799306841524603 := by
  apply lucas_primality 13807987799306841524603 (2 : ZMod 13807987799306841524603)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (433, 1), (12101, 1), (22332597053483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (433, 1), (12101, 1), (22332597053483, 1)] : List FactorBlock).map factorBlockValue).prod) = 13807987799306841524603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_59
      · exact prime_sixtyFourBJ_433
      · exact prime_sixtyFourBJ_12101
      · exact prime_sixtyFourBJ_22332597053483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13807987799306841524603) ^ 6903993899653420762301 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13807987799306841524603) ^ 234033691513675280078 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13807987799306841524603) ^ 31889117319415338394 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13807987799306841524603) ^ 1141061713850660402 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13807987799306841524603) ^ 618288494 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_18615036963738696164179 : Nat.Prime 18615036963738696164179 := by
  apply lucas_primality 18615036963738696164179 (3 : ZMod 18615036963738696164179)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (71, 1), (3972479078902837423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (71, 1), (3972479078902837423, 1)] : List FactorBlock).map factorBlockValue).prod) = 18615036963738696164179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_71
      · exact prime_sixtyFourBJ_3972479078902837423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18615036963738696164179) ^ 9307518481869348082089 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18615036963738696164179) ^ 6205012321246232054726 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18615036963738696164179) ^ 1692276087612608742198 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18615036963738696164179) ^ 262183619207587269918 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 18615036963738696164179) ^ 4686 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_23078071473344307355337 : Nat.Prime 23078071473344307355337 := by
  apply lucas_primality 23078071473344307355337 (3 : ZMod 23078071473344307355337)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (54429413852227139989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (54429413852227139989, 1)] : List FactorBlock).map factorBlockValue).prod) = 23078071473344307355337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_53
      · exact prime_sixtyFourBJ_54429413852227139989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23078071473344307355337) ^ 11539035736672153677668 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23078071473344307355337) ^ 435435310817817119912 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23078071473344307355337) ^ 424 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_23214021168741233727569 : Nat.Prime 23214021168741233727569 := by
  apply lucas_primality 23214021168741233727569 (3 : ZMod 23214021168741233727569)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (631, 1), (328475508953209669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (631, 1), (328475508953209669, 1)] : List FactorBlock).map factorBlockValue).prod) = 23214021168741233727569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_631
      · exact prime_sixtyFourBJ_328475508953209669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23214021168741233727569) ^ 11607010584370616863784 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23214021168741233727569) ^ 3316288738391604818224 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23214021168741233727569) ^ 36789257002759482928 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23214021168741233727569) ^ 70672 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_57055125140031011533717 : Nat.Prime 57055125140031011533717 := by
  apply lucas_primality 57055125140031011533717 (2 : ZMod 57055125140031011533717)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (41, 1), (157, 1), (359, 1), (187043565821111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (41, 1), (157, 1), (359, 1), (187043565821111, 1)] : List FactorBlock).map factorBlockValue).prod) = 57055125140031011533717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_41
      · exact prime_sixtyFourBJ_157
      · exact prime_sixtyFourBJ_359
      · exact prime_sixtyFourBJ_187043565821111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57055125140031011533717) ^ 28527562570015505766858 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 57055125140031011533717) ^ 19018375046677003844572 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 57055125140031011533717) ^ 5186829558184637412156 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 57055125140031011533717) ^ 1391588418049536866676 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 57055125140031011533717) ^ 363408440382363130788 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 57055125140031011533717) ^ 158927925181144878924 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 57055125140031011533717) ^ 305036556 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_58230156503301200941907 : Nat.Prime 58230156503301200941907 := by
  apply lucas_primality 58230156503301200941907 (2 : ZMod 58230156503301200941907)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (809, 1), (81833341, 1), (439783729237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (809, 1), (81833341, 1), (439783729237, 1)] : List FactorBlock).map factorBlockValue).prod) = 58230156503301200941907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_809
      · exact prime_sixtyFourBJ_81833341
      · exact prime_sixtyFourBJ_439783729237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58230156503301200941907) ^ 29115078251650600470953 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58230156503301200941907) ^ 71977943761806181634 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58230156503301200941907) ^ 711570073905466 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58230156503301200941907) ^ 132406345738 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_60468789924287726699363 : Nat.Prime 60468789924287726699363 := by
  apply lucas_primality 60468789924287726699363 (2 : ZMod 60468789924287726699363)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (13469, 1), (193937, 1), (218388309409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (13469, 1), (193937, 1), (218388309409, 1)] : List FactorBlock).map factorBlockValue).prod) = 60468789924287726699363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_53
      · exact prime_sixtyFourBJ_13469
      · exact prime_sixtyFourBJ_193937
      · exact prime_sixtyFourBJ_218388309409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60468789924287726699363) ^ 30234394962143863349681 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60468789924287726699363) ^ 1140920564609202390554 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60468789924287726699363) ^ 4489478797556442698 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60468789924287726699363) ^ 311796046779561026 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 60468789924287726699363) ^ 276886570018 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_68971342793161509100969 : Nat.Prime 68971342793161509100969 := by
  apply lucas_primality 68971342793161509100969 (11 : ZMod 68971342793161509100969)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (607, 1), (823, 1), (3947921, 1), (1457137247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (607, 1), (823, 1), (3947921, 1), (1457137247, 1)] : List FactorBlock).map factorBlockValue).prod) = 68971342793161509100969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_607
      · exact prime_sixtyFourBJ_823
      · exact prime_sixtyFourBJ_3947921
      · exact prime_sixtyFourBJ_1457137247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 68971342793161509100969) ^ 34485671396580754550484 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 68971342793161509100969) ^ 22990447597720503033656 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 68971342793161509100969) ^ 113626594387415995224 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 68971342793161509100969) ^ 83804790757182878616 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 68971342793161509100969) ^ 17470294565965608 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 68971342793161509100969) ^ 47333456704344 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_83964929942463168459811 : Nat.Prime 83964929942463168459811 := by
  apply lucas_primality 83964929942463168459811 (2 : ZMod 83964929942463168459811)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4027, 1), (30011, 1), (23158721431991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4027, 1), (30011, 1), (23158721431991, 1)] : List FactorBlock).map factorBlockValue).prod) = 83964929942463168459811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_4027
      · exact prime_sixtyFourBJ_30011
      · exact prime_sixtyFourBJ_23158721431991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83964929942463168459811) ^ 41982464971231584229905 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83964929942463168459811) ^ 27988309980821056153270 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83964929942463168459811) ^ 16792985988492633691962 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83964929942463168459811) ^ 20850491666864457030 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83964929942463168459811) ^ 2797805136198832710 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 83964929942463168459811) ^ 3625628910 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_115079970467803234556239 : Nat.Prime 115079970467803234556239 := by
  apply lucas_primality 115079970467803234556239 (3 : ZMod 115079970467803234556239)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (131, 1), (1645080631097624647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (131, 1), (1645080631097624647, 1)] : List FactorBlock).map factorBlockValue).prod) = 115079970467803234556239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_89
      · exact prime_sixtyFourBJ_131
      · exact prime_sixtyFourBJ_1645080631097624647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115079970467803234556239) ^ 57539985233901617278119 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 115079970467803234556239) ^ 38359990155934411518746 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 115079970467803234556239) ^ 1293033376042732972542 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 115079970467803234556239) ^ 878473057006131561498 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 115079970467803234556239) ^ 69954 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_120937579848575453398727 : Nat.Prime 120937579848575453398727 := by
  apply lucas_primality 120937579848575453398727 (5 : ZMod 120937579848575453398727)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (60468789924287726699363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (60468789924287726699363, 1)] : List FactorBlock).map factorBlockValue).prod) = 120937579848575453398727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_60468789924287726699363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 120937579848575453398727) ^ 60468789924287726699363 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 120937579848575453398727) ^ 2 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_459553842310494608049409 : Nat.Prime 459553842310494608049409 := by
  apply lucas_primality 459553842310494608049409 (23 : ZMod 459553842310494608049409)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (7, 1), (17, 1), (419, 1), (15359, 1), (781360147669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (7, 1), (17, 1), (419, 1), (15359, 1), (781360147669, 1)] : List FactorBlock).map factorBlockValue).prod) = 459553842310494608049409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_419
      · exact prime_sixtyFourBJ_15359
      · exact prime_sixtyFourBJ_781360147669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 459553842310494608049409) ^ 229776921155247304024704 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 459553842310494608049409) ^ 153184614103498202683136 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 459553842310494608049409) ^ 65650548901499229721344 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 459553842310494608049409) ^ 27032578959440859297024 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 459553842310494608049409) ^ 1096787213151538444032 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 459553842310494608049409) ^ 29920817912005638912 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (23 : ZMod 459553842310494608049409) ^ 588145996032 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3038880299714069911270619 : Nat.Prime 3038880299714069911270619 := by
  apply lucas_primality 3038880299714069911270619 (2 : ZMod 3038880299714069911270619)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2347, 1), (92485248636985510721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2347, 1), (92485248636985510721, 1)] : List FactorBlock).map factorBlockValue).prod) = 3038880299714069911270619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_2347
      · exact prime_sixtyFourBJ_92485248636985510721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3038880299714069911270619) ^ 1519440149857034955635309 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3038880299714069911270619) ^ 434125757102009987324374 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3038880299714069911270619) ^ 1294793480917797150094 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3038880299714069911270619) ^ 32858 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_9679554890953131216672271 : Nat.Prime 9679554890953131216672271 := by
  apply lucas_primality 9679554890953131216672271 (3 : ZMod 9679554890953131216672271)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (317, 1), (5233, 1), (21611336513322341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (317, 1), (5233, 1), (21611336513322341, 1)] : List FactorBlock).map factorBlockValue).prod) = 9679554890953131216672271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_317
      · exact prime_sixtyFourBJ_5233
      · exact prime_sixtyFourBJ_21611336513322341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9679554890953131216672271) ^ 4839777445476565608336135 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9679554890953131216672271) ^ 3226518296984377072224090 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9679554890953131216672271) ^ 1935910978190626243334454 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9679554890953131216672271) ^ 30534873473038268822310 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9679554890953131216672271) ^ 1849714292175259166190 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9679554890953131216672271) ^ 447892470 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_11655126399041994257659757 : Nat.Prime 11655126399041994257659757 := by
  apply lucas_primality 11655126399041994257659757 (2 : ZMod 11655126399041994257659757)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (56417, 1), (51647226895448155067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (56417, 1), (51647226895448155067, 1)] : List FactorBlock).map factorBlockValue).prod) = 11655126399041994257659757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_56417
      · exact prime_sixtyFourBJ_51647226895448155067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11655126399041994257659757) ^ 5827563199520997128829878 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655126399041994257659757) ^ 206588907581792620268 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655126399041994257659757) ^ 225668 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_37072552955698494228675719 : Nat.Prime 37072552955698494228675719 := by
  apply lucas_primality 37072552955698494228675719 (11 : ZMod 37072552955698494228675719)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (440711539871, 1), (1828690631723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (440711539871, 1), (1828690631723, 1)] : List FactorBlock).map factorBlockValue).prod) = 37072552955698494228675719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_440711539871
      · exact prime_sixtyFourBJ_1828690631723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 37072552955698494228675719) ^ 18536276477849247114337859 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 37072552955698494228675719) ^ 1611850128508630183855466 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 37072552955698494228675719) ^ 84119769059258 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (11 : ZMod 37072552955698494228675719) ^ 20272730834066 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_38526008443269158208109543 : Nat.Prime 38526008443269158208109543 := by
  apply lucas_primality 38526008443269158208109543 (5 : ZMod 38526008443269158208109543)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3119, 1), (2058673102664804863103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3119, 1), (2058673102664804863103, 1)] : List FactorBlock).map factorBlockValue).prod) = 38526008443269158208109543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_3119
      · exact prime_sixtyFourBJ_2058673102664804863103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 38526008443269158208109543) ^ 19263004221634579104054771 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 38526008443269158208109543) ^ 12842002814423052736036514 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 38526008443269158208109543) ^ 12352038615988829178618 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 38526008443269158208109543) ^ 18714 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_43385940701021001560049967 : Nat.Prime 43385940701021001560049967 := by
  apply lucas_primality 43385940701021001560049967 (3 : ZMod 43385940701021001560049967)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (331339, 1), (4599857, 1), (37357444441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (331339, 1), (4599857, 1), (37357444441, 1)] : List FactorBlock).map factorBlockValue).prod) = 43385940701021001560049967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_127
      · exact prime_sixtyFourBJ_331339
      · exact prime_sixtyFourBJ_4599857
      · exact prime_sixtyFourBJ_37357444441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43385940701021001560049967) ^ 21692970350510500780024983 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43385940701021001560049967) ^ 14461980233673667186683322 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43385940701021001560049967) ^ 341621580323000012283858 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43385940701021001560049967) ^ 130941243563302241994 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43385940701021001560049967) ^ 9432019452131012238 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 43385940701021001560049967) ^ 1161373358114526 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_68105383062628826931347563 : Nat.Prime 68105383062628826931347563 := by
  apply lucas_primality 68105383062628826931347563 (2 : ZMod 68105383062628826931347563)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (173, 1), (1983892909, 1), (14810752967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (173, 1), (1983892909, 1), (14810752967, 1)] : List FactorBlock).map factorBlockValue).prod) = 68105383062628826931347563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_29
      · exact prime_sixtyFourBJ_173
      · exact prime_sixtyFourBJ_1983892909
      · exact prime_sixtyFourBJ_14810752967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68105383062628826931347563) ^ 34052691531314413465673781 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68105383062628826931347563) ^ 22701794354209608977115854 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68105383062628826931347563) ^ 9729340437518403847335366 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68105383062628826931347563) ^ 6191398460238984266486142 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68105383062628826931347563) ^ 2348461484918235411425778 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68105383062628826931347563) ^ 393672734466062583418194 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68105383062628826931347563) ^ 34329163007572818 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68105383062628826931347563) ^ 4598374114697286 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_201236916443033581704061549 : Nat.Prime 201236916443033581704061549 := by
  apply lucas_primality 201236916443033581704061549 (6 : ZMod 201236916443033581704061549)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (107, 1), (1731572501, 1), (3935266187689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (107, 1), (1731572501, 1), (3935266187689, 1)] : List FactorBlock).map factorBlockValue).prod) = 201236916443033581704061549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_23
      · exact prime_sixtyFourBJ_107
      · exact prime_sixtyFourBJ_1731572501
      · exact prime_sixtyFourBJ_3935266187689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 201236916443033581704061549) ^ 100618458221516790852030774 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 201236916443033581704061549) ^ 67078972147677860568020516 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 201236916443033581704061549) ^ 8749431149697112248002676 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 201236916443033581704061549) ^ 1880718845261996090692164 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 201236916443033581704061549) ^ 116216281054831548 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (6 : ZMod 201236916443033581704061549) ^ 51136799099532 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_307581628384474092360679441 : Nat.Prime 307581628384474092360679441 := by
  apply lucas_primality 307581628384474092360679441 (7 : ZMod 307581628384474092360679441)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (1831, 1), (63630908011947870091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (1831, 1), (63630908011947870091, 1)] : List FactorBlock).map factorBlockValue).prod) = 307581628384474092360679441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_11
      · exact prime_sixtyFourBJ_1831
      · exact prime_sixtyFourBJ_63630908011947870091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 307581628384474092360679441) ^ 153790814192237046180339720 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 307581628384474092360679441) ^ 102527209461491364120226480 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 307581628384474092360679441) ^ 61516325676894818472135888 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 307581628384474092360679441) ^ 27961966216770372032789040 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 307581628384474092360679441) ^ 167985597151542377040240 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (7 : ZMod 307581628384474092360679441) ^ 4833840 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_320614748231273842036979417 : Nat.Prime 320614748231273842036979417 := by
  apply lucas_primality 320614748231273842036979417 (3 : ZMod 320614748231273842036979417)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (89, 1), (128047627, 1), (185088044451811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (89, 1), (128047627, 1), (185088044451811, 1)] : List FactorBlock).map factorBlockValue).prod) = 320614748231273842036979417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_89
      · exact prime_sixtyFourBJ_128047627
      · exact prime_sixtyFourBJ_185088044451811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 320614748231273842036979417) ^ 160307374115636921018489708 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 320614748231273842036979417) ^ 16874460433224939054577864 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 320614748231273842036979417) ^ 3602412901474986989179544 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 320614748231273842036979417) ^ 2503871065344099208 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 320614748231273842036979417) ^ 1732228298056 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_330415199050570422361253897 : Nat.Prime 330415199050570422361253897 := by
  apply lucas_primality 330415199050570422361253897 (3 : ZMod 330415199050570422361253897)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5897, 1), (12583, 1), (556614742937437087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5897, 1), (12583, 1), (556614742937437087, 1)] : List FactorBlock).map factorBlockValue).prod) = 330415199050570422361253897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5897
      · exact prime_sixtyFourBJ_12583
      · exact prime_sixtyFourBJ_556614742937437087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 330415199050570422361253897) ^ 165207599525285211180626948 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 330415199050570422361253897) ^ 56031066483054166925768 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 330415199050570422361253897) ^ 26258857112816532016312 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 330415199050570422361253897) ^ 593615608 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_413470385697161894648782199 : Nat.Prime 413470385697161894648782199 := by
  apply lucas_primality 413470385697161894648782199 (17 : ZMod 413470385697161894648782199)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (10987, 1), (115437705156613391579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (10987, 1), (115437705156613391579, 1)] : List FactorBlock).map factorBlockValue).prod) = 413470385697161894648782199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_163
      · exact prime_sixtyFourBJ_10987
      · exact prime_sixtyFourBJ_115437705156613391579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 413470385697161894648782199) ^ 206735192848580947324391099 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 413470385697161894648782199) ^ 2536628133111422666556946 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 413470385697161894648782199) ^ 37632691881055965654754 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (17 : ZMod 413470385697161894648782199) ^ 3581762 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_434856784957359923682339899 : Nat.Prime 434856784957359923682339899 := by
  apply lucas_primality 434856784957359923682339899 (2 : ZMod 434856784957359923682339899)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (331, 1), (593, 1), (58301531992791279037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (331, 1), (593, 1), (58301531992791279037, 1)] : List FactorBlock).map factorBlockValue).prod) = 434856784957359923682339899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_19
      · exact prime_sixtyFourBJ_331
      · exact prime_sixtyFourBJ_593
      · exact prime_sixtyFourBJ_58301531992791279037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 434856784957359923682339899) ^ 217428392478679961841169949 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 434856784957359923682339899) ^ 22887199208282101246438942 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 434856784957359923682339899) ^ 1313766721925558681819758 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 434856784957359923682339899) ^ 733316669405328707727386 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 434856784957359923682339899) ^ 7458754 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_458576245955034101337740257 : Nat.Prime 458576245955034101337740257 := by
  apply lucas_primality 458576245955034101337740257 (15 : ZMod 458576245955034101337740257)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (41, 1), (1831, 1), (63630908011947870091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (41, 1), (1831, 1), (63630908011947870091, 1)] : List FactorBlock).map factorBlockValue).prod) = 458576245955034101337740257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_41
      · exact prime_sixtyFourBJ_1831
      · exact prime_sixtyFourBJ_63630908011947870091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 458576245955034101337740257) ^ 229288122977517050668870128 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (15 : ZMod 458576245955034101337740257) ^ 152858748651678033779246752 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (15 : ZMod 458576245955034101337740257) ^ 11184786486708148813115616 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (15 : ZMod 458576245955034101337740257) ^ 250451253935026816678176 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (15 : ZMod 458576245955034101337740257) ^ 7206816 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_850169444748096929446372387 : Nat.Prime 850169444748096929446372387 := by
  apply lucas_primality 850169444748096929446372387 (3 : ZMod 850169444748096929446372387)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (89, 1), (571, 1), (75357486244512801877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (89, 1), (571, 1), (75357486244512801877, 1)] : List FactorBlock).map factorBlockValue).prod) = 850169444748096929446372387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_37
      · exact prime_sixtyFourBJ_89
      · exact prime_sixtyFourBJ_571
      · exact prime_sixtyFourBJ_75357486244512801877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 850169444748096929446372387) ^ 425084722374048464723186193 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 850169444748096929446372387) ^ 283389814916032309815457462 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 850169444748096929446372387) ^ 22977552560759376471523578 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 850169444748096929446372387) ^ 9552465671326931791532274 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 850169444748096929446372387) ^ 1488913213219083939485766 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 850169444748096929446372387) ^ 11281818 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2364533768205644585022723203 : Nat.Prime 2364533768205644585022723203 := by
  apply lucas_primality 2364533768205644585022723203 (2 : ZMod 2364533768205644585022723203)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (50929, 1), (23214021168741233727569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (50929, 1), (23214021168741233727569, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644585022723203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_50929
      · exact prime_sixtyFourBJ_23214021168741233727569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2364533768205644585022723203) ^ 1182266884102822292511361601 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364533768205644585022723203) ^ 46428042337482467455138 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364533768205644585022723203) ^ 101858 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_2802410391947430619286190461 : Nat.Prime 2802410391947430619286190461 := by
  apply lucas_primality 2802410391947430619286190461 (2 : ZMod 2802410391947430619286190461)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (173, 1), (5693, 1), (22717, 1), (368395700330263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (173, 1), (5693, 1), (22717, 1), (368395700330263, 1)] : List FactorBlock).map factorBlockValue).prod) = 2802410391947430619286190461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_5
      · exact prime_sixtyFourBJ_17
      · exact prime_sixtyFourBJ_173
      · exact prime_sixtyFourBJ_5693
      · exact prime_sixtyFourBJ_22717
      · exact prime_sixtyFourBJ_368395700330263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2802410391947430619286190461) ^ 1401205195973715309643095230 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2802410391947430619286190461) ^ 560482078389486123857238092 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2802410391947430619286190461) ^ 164847670114554742310952380 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2802410391947430619286190461) ^ 16198903999696130747319020 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2802410391947430619286190461) ^ 492255470217360024466220 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2802410391947430619286190461) ^ 123361816786874614574380 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2802410391947430619286190461) ^ 7607065960420 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_3152711690940859446696964267 : Nat.Prime 3152711690940859446696964267 := by
  apply lucas_primality 3152711690940859446696964267 (2 : ZMod 3152711690940859446696964267)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4297, 1), (7420951, 1), (16478136236832713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4297, 1), (7420951, 1), (16478136236832713, 1)] : List FactorBlock).map factorBlockValue).prod) = 3152711690940859446696964267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_4297
      · exact prime_sixtyFourBJ_7420951
      · exact prime_sixtyFourBJ_16478136236832713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3152711690940859446696964267) ^ 1576355845470429723348482133 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3152711690940859446696964267) ^ 1050903896980286482232321422 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3152711690940859446696964267) ^ 733700649509159750220378 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3152711690940859446696964267) ^ 424839308458021006566 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3152711690940859446696964267) ^ 191326958682 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_6878643689325511520066103859 : Nat.Prime 6878643689325511520066103859 := by
  apply lucas_primality 6878643689325511520066103859 (3 : ZMod 6878643689325511520066103859)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (1658963, 1), (4346280376733129279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (1658963, 1), (4346280376733129279, 1)] : List FactorBlock).map factorBlockValue).prod) = 6878643689325511520066103859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_53
      · exact prime_sixtyFourBJ_1658963
      · exact prime_sixtyFourBJ_4346280376733129279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6878643689325511520066103859) ^ 3439321844662755760033051929 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6878643689325511520066103859) ^ 2292881229775170506688701286 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6878643689325511520066103859) ^ 129785729987273802265398186 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6878643689325511520066103859) ^ 4146351479403405332166 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6878643689325511520066103859) ^ 1582650702 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_37832540291290313360363571217 : Nat.Prime 37832540291290313360363571217 := by
  apply lucas_primality 37832540291290313360363571217 (10 : ZMod 37832540291290313360363571217)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (8017, 1), (32933, 1), (426464659968860521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (8017, 1), (32933, 1), (426464659968860521, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290313360363571217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_7
      · exact prime_sixtyFourBJ_8017
      · exact prime_sixtyFourBJ_32933
      · exact prime_sixtyFourBJ_426464659968860521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 37832540291290313360363571217) ^ 18916270145645156680181785608 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 37832540291290313360363571217) ^ 12610846763763437786787857072 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 37832540291290313360363571217) ^ 5404648613041473337194795888 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 37832540291290313360363571217) ^ 4719039577309506468799248 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 37832540291290313360363571217) ^ 1148772972134039211743952 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (10 : ZMod 37832540291290313360363571217) ^ 88712017296 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_37832540291290313360363571247 : Nat.Prime 37832540291290313360363571247 := by
  apply lucas_primality 37832540291290313360363571247 (3 : ZMod 37832540291290313360363571247)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 2), (67, 1), (337, 1), (577, 1), (209702833, 1), (4552201517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 2), (67, 1), (337, 1), (577, 1), (209702833, 1), (4552201517, 1)] : List FactorBlock).map factorBlockValue).prod) = 37832540291290313360363571247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_13
      · exact prime_sixtyFourBJ_67
      · exact prime_sixtyFourBJ_337
      · exact prime_sixtyFourBJ_577
      · exact prime_sixtyFourBJ_209702833
      · exact prime_sixtyFourBJ_4552201517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37832540291290313360363571247) ^ 18916270145645156680181785623 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290313360363571247) ^ 12610846763763437786787857082 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290313360363571247) ^ 2910195407022331796951043942 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290313360363571247) ^ 564664780467019602393486138 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290313360363571247) ^ 112262730834689357152414158 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290313360363571247) ^ 65567660816794303917441198 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290313360363571247) ^ 180410248874846213262 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37832540291290313360363571247) ^ 8310822829351100838 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem prime_sixtyFourBJ_75665080582580626720727142457 : Nat.Prime 75665080582580626720727142457 := by
  apply lucas_primality 75665080582580626720727142457 (5 : ZMod 75665080582580626720727142457)
  · rw [← sixtyFourBJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (6353, 1), (144899, 1), (1141612614338177909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (6353, 1), (144899, 1), (1141612614338177909, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFourBJ_2
      · exact prime_sixtyFourBJ_3
      · exact prime_sixtyFourBJ_6353
      · exact prime_sixtyFourBJ_144899
      · exact prime_sixtyFourBJ_1141612614338177909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 75665080582580626720727142457) ^ 37832540291290313360363571228 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 75665080582580626720727142457) ^ 25221693527526875573575714152 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 75665080582580626720727142457) ^ 11910133886759110140205752 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 75665080582580626720727142457) ^ 522191875600111986423144 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide
    · change (5 : ZMod 75665080582580626720727142457) ^ 66279120984 ≠ 1
      rw [← sixtyFourBJFastPow_eq_pow]
      decide

private theorem phi_sixtyFourBJ_75665080582580626720727142400 : Nat.totient 75665080582580626720727142400 = 30263533283938164774841221120 := by
  rw [← show ((([(2, 12), (5, 2), (12263, 1), (980299, 1), (61466750512373, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_12263, prime_sixtyFourBJ_980299, prime_sixtyFourBJ_61466750512373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142401 : Nat.totient 75665080582580626720727142401 = 69844689768320861981902368912 := by
  rw [← show ((([(13, 1), (324712149019, 1), (17924770698074783, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_13, prime_sixtyFourBJ_324712149019, prime_sixtyFourBJ_17924770698074783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142402 : Nat.totient 75665080582580626720727142402 = 25221690127318707354219352920 := by
  rw [← show ((([(2, 1), (3, 2), (7417691, 1), (566701361369885309179, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_7417691, prime_sixtyFourBJ_566701361369885309179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142403 : Nat.totient 75665080582580626720727142403 = 71212675833248523575441817600 := by
  rw [← show ((([(17, 1), (83621, 1), (129313, 1), (617521, 1), (666557013223, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_17, prime_sixtyFourBJ_83621, prime_sixtyFourBJ_129313, prime_sixtyFourBJ_617521, prime_sixtyFourBJ_666557013223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142404 : Nat.totient 75665080582580626720727142404 = 29964499137169784691714662400 := by
  rw [← show ((([(2, 2), (7, 1), (19, 1), (41, 1), (6397, 1), (11273, 1), (1414331, 1), (34012072147, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_7, prime_sixtyFourBJ_19, prime_sixtyFourBJ_41, prime_sixtyFourBJ_6397, prime_sixtyFourBJ_11273, prime_sixtyFourBJ_1414331, prime_sixtyFourBJ_34012072147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142405 : Nat.totient 75665080582580626720727142405 = 36686099676402728107019220480 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (458576245955034101337740257, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_5, prime_sixtyFourBJ_11, prime_sixtyFourBJ_458576245955034101337740257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142406 : Nat.totient 75665080582580626720727142406 = 36612135422182196600749626240 := by
  rw [← show ((([(2, 1), (31, 1), (106559917, 1), (11452754092568352689, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_31, prime_sixtyFourBJ_106559917, prime_sixtyFourBJ_11452754092568352689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142407 : Nat.totient 75665080582580626720727142407 = 75655401027689673589510462320 := by
  rw [← show ((([(7817, 1), (9679554890953131216672271, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_7817, prime_sixtyFourBJ_9679554890953131216672271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142408 : Nat.totient 75665080582580626720727142408 = 25221693527526875573575714128 := by
  rw [← show ((([(2, 3), (3, 1), (3152711690940859446696964267, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_3152711690940859446696964267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142409 : Nat.totient 75665080582580626720727142409 = 75532589374252157052196879776 := by
  rw [← show ((([(643, 1), (5099, 1), (23078071473344307355337, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_643, prime_sixtyFourBJ_5099, prime_sixtyFourBJ_23078071473344307355337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142410 : Nat.totient 75665080582580626720727142410 = 29972187259763054052452226048 := by
  rw [← show ((([(2, 1), (5, 1), (103, 1), (225576709783, 1), (325659698444609, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_103, prime_sixtyFourBJ_225576709783, prime_sixtyFourBJ_325659698444609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142411 : Nat.totient 75665080582580626720727142411 = 42995640260229834669554185344 := by
  rw [← show ((([(3, 2), (7, 1), (179, 1), (418502137, 1), (16032610377286639, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_7, prime_sixtyFourBJ_179, prime_sixtyFourBJ_418502137, prime_sixtyFourBJ_16032610377286639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142412 : Nat.totient 75665080582580626720727142412 = 37191310794827765676289612256 := by
  rw [← show ((([(2, 2), (59, 1), (320614748231273842036979417, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_59, prime_sixtyFourBJ_320614748231273842036979417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142413 : Nat.totient 75665080582580626720727142413 = 75334665383530056298365888288 := by
  rw [← show ((([(229, 1), (330415199050570422361253897, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_229, prime_sixtyFourBJ_330415199050570422361253897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142414 : Nat.totient 75665080582580626720727142414 = 23281563256174345968568200672 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (5577011752699, 1), (173939948253587, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_13, prime_sixtyFourBJ_5577011752699, prime_sixtyFourBJ_173939948253587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142415 : Nat.totient 75665080582580626720727142415 = 60532009234113304149211231680 := by
  rw [← show ((([(5, 1), (1095961, 1), (13807987799306841524603, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_5, prime_sixtyFourBJ_1095961, prime_sixtyFourBJ_13807987799306841524603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142416 : Nat.totient 75665080582580626720727142416 = 32897713320006316337864000000 := by
  rw [← show ((([(2, 4), (11, 1), (23, 1), (239597, 1), (3133751, 1), (24894828203711, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_11, prime_sixtyFourBJ_23, prime_sixtyFourBJ_239597, prime_sixtyFourBJ_3133751, prime_sixtyFourBJ_24894828203711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142417 : Nat.totient 75665080582580626720727142417 = 49616446283659427357853863760 := by
  rw [← show ((([(3, 1), (61, 1), (413470385697161894648782199, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_61, prime_sixtyFourBJ_413470385697161894648782199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142418 : Nat.totient 75665080582580626720727142418 = 31622084567116010162537545728 := by
  rw [← show ((([(2, 1), (7, 1), (43, 2), (613, 1), (1405961729, 1), (3391537149019, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_7, prime_sixtyFourBJ_43, prime_sixtyFourBJ_613, prime_sixtyFourBJ_1405961729, prime_sixtyFourBJ_3391537149019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142419 : Nat.totient 75665080582580626720727142419 = 75665011611237833559216944400 := by
  rw [← show ((([(1097051, 1), (68971342793161509100969, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_1097051, prime_sixtyFourBJ_68971342793161509100969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142420 : Nat.totient 75665080582580626720727142420 = 18876532748177603133218783232 := by
  rw [← show ((([(2, 2), (3, 3), (5, 1), (17, 1), (173, 1), (5693, 1), (22717, 1), (368395700330263, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_5, prime_sixtyFourBJ_17, prime_sixtyFourBJ_173, prime_sixtyFourBJ_5693, prime_sixtyFourBJ_22717, prime_sixtyFourBJ_368395700330263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142421 : Nat.totient 75665080582580626720727142421 = 75650275575597712844213112000 := by
  rw [← show ((([(5521, 1), (68771, 1), (199283991101396887031, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_5521, prime_sixtyFourBJ_68771, prime_sixtyFourBJ_199283991101396887031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142422 : Nat.totient 75665080582580626720727142422 = 37497739043048148449912675712 := by
  rw [← show ((([(2, 1), (113, 1), (5574777079, 1), (60056435759024093, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_113, prime_sixtyFourBJ_5574777079, prime_sixtyFourBJ_60056435759024093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142423 : Nat.totient 75665080582580626720727142423 = 47788471945050679879042284864 := by
  rw [← show ((([(3, 1), (19, 1), (25938915193, 1), (51176294158924423, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_19, prime_sixtyFourBJ_25938915193, prime_sixtyFourBJ_51176294158924423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142424 : Nat.totient 75665080582580626720727142424 = 37027592625518179033547324832 := by
  rw [← show ((([(2, 3), (47, 1), (201236916443033581704061549, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_47, prime_sixtyFourBJ_201236916443033581704061549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142425 : Nat.totient 75665080582580626720727142425 = 51110225940281245121473689600 := by
  rw [← show ((([(5, 2), (7, 2), (67, 1), (17772977, 1), (190554941, 1), (272210087, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_5, prime_sixtyFourBJ_7, prime_sixtyFourBJ_67, prime_sixtyFourBJ_17772977, prime_sixtyFourBJ_190554941, prime_sixtyFourBJ_272210087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142426 : Nat.totient 75665080582580626720727142426 = 24351979957612155726211034288 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (434856784957359923682339899, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_29, prime_sixtyFourBJ_434856784957359923682339899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142427 : Nat.totient 75665080582580626720727142427 = 63360920077899406807796121600 := by
  rw [← show ((([(11, 1), (13, 1), (823, 1), (1861, 1), (2753, 1), (121904933, 1), (1029403787, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_11, prime_sixtyFourBJ_13, prime_sixtyFourBJ_823, prime_sixtyFourBJ_1861, prime_sixtyFourBJ_2753, prime_sixtyFourBJ_121904933, prime_sixtyFourBJ_1029403787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142428 : Nat.totient 75665080582580626720727142428 = 36810039098309716134652414464 := by
  rw [← show ((([(2, 2), (37, 1), (353851483, 1), (1444816735378486817, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_37, prime_sixtyFourBJ_353851483, prime_sixtyFourBJ_1444816735378486817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142429 : Nat.totient 75665080582580626720727142429 = 50423464670373010378656552960 := by
  rw [← show ((([(3, 2), (2593, 1), (107581, 1), (30138032428908424057, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_2593, prime_sixtyFourBJ_107581, prime_sixtyFourBJ_30138032428908424057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142430 : Nat.totient 75665080582580626720727142430 = 30095553397980152591017850880 := by
  rw [← show ((([(2, 1), (5, 1), (199, 1), (2297, 1), (6089, 1), (89939, 1), (30226467755111, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_199, prime_sixtyFourBJ_2297, prime_sixtyFourBJ_6089, prime_sixtyFourBJ_89939, prime_sixtyFourBJ_30226467755111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142431 : Nat.totient 75665080582580626720727142431 = 74977061264653087280563200000 := by
  rw [← show ((([(181, 1), (281, 1), (37321, 1), (398611, 1), (100001854277041, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_181, prime_sixtyFourBJ_281, prime_sixtyFourBJ_37321, prime_sixtyFourBJ_398611, prime_sixtyFourBJ_100001854277041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142432 : Nat.totient 75665080582580626720727142432 = 21615241498304568843155374080 := by
  rw [← show ((([(2, 5), (3, 1), (7, 1), (8017, 1), (32933, 1), (426464659968860521, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_7, prime_sixtyFourBJ_8017, prime_sixtyFourBJ_32933, prime_sixtyFourBJ_426464659968860521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142433 : Nat.totient 75665080582580626720727142433 = 75607798908861388624436044800 := by
  rw [← show ((([(1321, 1), (24904721, 1), (2299910841680460713, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_1321, prime_sixtyFourBJ_24904721, prime_sixtyFourBJ_2299910841680460713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142434 : Nat.totient 75665080582580626720727142434 = 37832540291290313360363571216 := by
  rw [← show ((([(2, 1), (37832540291290313360363571217, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_37832540291290313360363571217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142435 : Nat.totient 75665080582580626720727142435 = 40321965012740250961349030400 := by
  rw [← show ((([(3, 1), (5, 1), (1301, 1), (23357, 1), (166000685924635783597, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_5, prime_sixtyFourBJ_1301, prime_sixtyFourBJ_23357, prime_sixtyFourBJ_166000685924635783597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142436 : Nat.totient 75665080582580626720727142436 = 37568110399015059209469024000 := by
  rw [← show ((([(2, 2), (151, 1), (2707, 1), (8248042681, 1), (5610730450477, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_151, prime_sixtyFourBJ_2707, prime_sixtyFourBJ_8248042681, prime_sixtyFourBJ_5610730450477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142437 : Nat.totient 75665080582580626720727142437 = 68883261937031124547815997440 := by
  rw [← show ((([(17, 1), (31, 1), (2099, 1), (79537, 1), (398144713, 1), (2160042449, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_17, prime_sixtyFourBJ_31, prime_sixtyFourBJ_2099, prime_sixtyFourBJ_79537, prime_sixtyFourBJ_398144713, prime_sixtyFourBJ_2160042449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142438 : Nat.totient 75665080582580626720727142438 = 22496179637399350313463040320 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (53, 1), (1658963, 1), (4346280376733129279, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_11, prime_sixtyFourBJ_53, prime_sixtyFourBJ_1658963, prime_sixtyFourBJ_4346280376733129279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142439 : Nat.totient 75665080582580626720727142439 = 61812962132234484192040052352 := by
  rw [← show ((([(7, 1), (23, 1), (349, 1), (1367, 1), (985089480472584496453, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_7, prime_sixtyFourBJ_23, prime_sixtyFourBJ_349, prime_sixtyFourBJ_1367, prime_sixtyFourBJ_985089480472584496453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142440 : Nat.totient 75665080582580626720727142440 = 27555097238244550183976626176 := by
  rw [← show ((([(2, 3), (5, 1), (13, 1), (73, 1), (404983, 1), (4921896784205167883, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_13, prime_sixtyFourBJ_73, prime_sixtyFourBJ_404983, prime_sixtyFourBJ_4921896784205167883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142441 : Nat.totient 75665080582580626720727142441 = 49668579276918257237980016640 := by
  rw [← show ((([(3, 1), (71, 1), (773, 1), (459553842310494608049409, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_71, prime_sixtyFourBJ_773, prime_sixtyFourBJ_459553842310494608049409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142442 : Nat.totient 75665080582580626720727142442 = 35802352008071368422158808000 := by
  rw [← show ((([(2, 1), (19, 1), (941, 1), (39199, 1), (53981791190061936301, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_19, prime_sixtyFourBJ_941, prime_sixtyFourBJ_39199, prime_sixtyFourBJ_53981791190061936301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142443 : Nat.totient 75665080582580626720727142443 = 74814911137832529791280769968 := by
  rw [← show ((([(89, 1), (850169444748096929446372387, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_89, prime_sixtyFourBJ_850169444748096929446372387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142444 : Nat.totient 75665080582580626720727142444 = 25175073021930707596545072960 := by
  rw [← show ((([(2, 2), (3, 1), (541, 1), (11655126399041994257659757, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_541, prime_sixtyFourBJ_11655126399041994257659757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142445 : Nat.totient 75665080582580626720727142445 = 59053829510795540123795558400 := by
  rw [← show ((([(5, 1), (41, 1), (32507, 1), (2425453, 1), (36287689, 1), (129006791, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_5, prime_sixtyFourBJ_41, prime_sixtyFourBJ_32507, prime_sixtyFourBJ_2425453, prime_sixtyFourBJ_36287689, prime_sixtyFourBJ_129006791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142446 : Nat.totient 75665080582580626720727142446 = 32337562858635212122799721312 := by
  rw [← show ((([(2, 1), (7, 1), (359, 1), (75109709, 1), (200436557578066819, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_7, prime_sixtyFourBJ_359, prime_sixtyFourBJ_75109709, prime_sixtyFourBJ_200436557578066819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142447 : Nat.totient 75665080582580626720727142447 = 50443387055053751147151428280 := by
  rw [← show ((([(3, 3), (2802410391947430619286190461, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_2802410391947430619286190461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142448 : Nat.totient 75665080582580626720727142448 = 37485452765682145347883170624 := by
  rw [← show ((([(2, 4), (109, 1), (43385940701021001560049967, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_109, prime_sixtyFourBJ_43385940701021001560049967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142449 : Nat.totient 75665080582580626720727142449 = 68786436893255115200661038580 := by
  rw [← show ((([(11, 1), (6878643689325511520066103859, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_11, prime_sixtyFourBJ_6878643689325511520066103859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142450 : Nat.totient 75665080582580626720727142450 = 20177288844358678018595841600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (305821, 1), (1649441570561006312423, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_5, prime_sixtyFourBJ_305821, prime_sixtyFourBJ_1649441570561006312423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142451 : Nat.totient 75665080582580626720727142451 = 75247079002174215362029900320 := by
  rw [← show ((([(239, 1), (743, 1), (591447133, 1), (720431764976311, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_239, prime_sixtyFourBJ_743, prime_sixtyFourBJ_591447133, prime_sixtyFourBJ_720431764976311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142452 : Nat.totient 75665080582580626720727142452 = 37755488274403775043947351160 := by
  rw [← show ((([(2, 2), (491, 1), (38526008443269158208109543, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_491, prime_sixtyFourBJ_38526008443269158208109543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142453 : Nat.totient 75665080582580626720727142453 = 39499792118521915012899489792 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (97, 1), (13260067, 1), (215484183812838839, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_7, prime_sixtyFourBJ_13, prime_sixtyFourBJ_97, prime_sixtyFourBJ_13260067, prime_sixtyFourBJ_215484183812838839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142454 : Nat.totient 75665080582580626720727142454 = 35607023657619691831752957696 := by
  rw [← show ((([(2, 1), (17, 2), (487187, 1), (268702662251865000889, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_17, prime_sixtyFourBJ_487187, prime_sixtyFourBJ_268702662251865000889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142455 : Nat.totient 75665080582580626720727142455 = 58444216832014806595216041600 := by
  rw [← show ((([(5, 1), (29, 1), (109229, 1), (4777377271135247126851, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_5, prime_sixtyFourBJ_29, prime_sixtyFourBJ_109229, prime_sixtyFourBJ_4777377271135247126851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142456 : Nat.totient 75665080582580626720727142456 = 25217549446338125221560364032 := by
  rw [← show ((([(2, 3), (3, 2), (6353, 1), (144899, 1), (1141612614338177909, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_6353, prime_sixtyFourBJ_144899, prime_sixtyFourBJ_1141612614338177909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142457 : Nat.totient 75665080582580626720727142457 = 75665080582580626720727142456 := by
  rw [← show ((([(75665080582580626720727142457, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_75665080582580626720727142457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142458 : Nat.totient 75665080582580626720727142458 = 37366809671293449289324764576 := by
  rw [← show ((([(2, 1), (83, 1), (3769, 1), (120937579848575453398727, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_83, prime_sixtyFourBJ_3769, prime_sixtyFourBJ_120937579848575453398727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142459 : Nat.totient 75665080582580626720727142459 = 49685839442613475301644782624 := by
  rw [← show ((([(3, 1), (79, 1), (419, 1), (315059, 1), (2418472980383135167, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_79, prime_sixtyFourBJ_419, prime_sixtyFourBJ_315059, prime_sixtyFourBJ_2418472980383135167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142460 : Nat.totient 75665080582580626720727142460 = 23441599825200593057759232000 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (11, 1), (167, 1), (21401, 1), (4776113, 1), (2878390061969, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_7, prime_sixtyFourBJ_11, prime_sixtyFourBJ_167, prime_sixtyFourBJ_21401, prime_sixtyFourBJ_4776113, prime_sixtyFourBJ_2878390061969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142461 : Nat.totient 75665080582580626720727142461 = 69952190714225375201889228720 := by
  rw [← show ((([(19, 1), (43, 1), (1103, 1), (83964929942463168459811, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_19, prime_sixtyFourBJ_43, prime_sixtyFourBJ_1103, prime_sixtyFourBJ_83964929942463168459811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142462 : Nat.totient 75665080582580626720727142462 = 24125006543587081555702856544 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (397543, 1), (780047, 1), (1768119162085819, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_23, prime_sixtyFourBJ_397543, prime_sixtyFourBJ_780047, prime_sixtyFourBJ_1768119162085819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142463 : Nat.totient 75665080582580626720727142463 = 75514652752407847550390868504 := by
  rw [← show ((([(503, 1), (321912683, 1), (467293162200793387, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_503, prime_sixtyFourBJ_321912683, prime_sixtyFourBJ_467293162200793387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142464 : Nat.totient 75665080582580626720727142464 = 37831797442612913640882659328 := by
  rw [← show ((([(2, 6), (50929, 1), (23214021168741233727569, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_50929, prime_sixtyFourBJ_23214021168741233727569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142465 : Nat.totient 75665080582580626720727142465 = 39264041815569007712463904128 := by
  rw [← show ((([(3, 2), (5, 1), (37, 1), (153086609887, 1), (296854786162783, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_5, prime_sixtyFourBJ_37, prime_sixtyFourBJ_153086609887, prime_sixtyFourBJ_296854786162783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142466 : Nat.totient 75665080582580626720727142466 = 34873360359481455986053704960 := by
  rw [← show ((([(2, 1), (13, 1), (733, 1), (25997, 1), (152719657757883376141, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_13, prime_sixtyFourBJ_733, prime_sixtyFourBJ_25997, prime_sixtyFourBJ_152719657757883376141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142467 : Nat.totient 75665080582580626720727142467 = 64855783303165866388574453184 := by
  rw [← show ((([(7, 1), (1216080589, 1), (8888635608411102329, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_7, prime_sixtyFourBJ_1216080589, prime_sixtyFourBJ_8888635608411102329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142468 : Nat.totient 75665080582580626720727142468 = 24404363058381642285991848000 := by
  rw [← show ((([(2, 2), (3, 1), (31, 2), (6571, 1), (1886659, 1), (529256239084891, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_31, prime_sixtyFourBJ_6571, prime_sixtyFourBJ_1886659, prime_sixtyFourBJ_529256239084891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142469 : Nat.totient 75665080582580626720727142469 = 75665080215199686513839677440 := by
  rw [← show ((([(230611841, 1), (1948838897, 1), (168359627797, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_230611841, prime_sixtyFourBJ_1948838897, prime_sixtyFourBJ_168359627797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142470 : Nat.totient 75665080582580626720727142470 = 30265858171803684016147138560 := by
  rw [← show ((([(2, 1), (5, 1), (198013, 1), (1900433, 1), (5734231, 1), (3506501653, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_198013, prime_sixtyFourBJ_1900433, prime_sixtyFourBJ_5734231, prime_sixtyFourBJ_3506501653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142471 : Nat.totient 75665080582580626720727142471 = 41524316532445257286029337600 := by
  rw [← show ((([(3, 1), (11, 2), (17, 1), (47, 1), (59, 1), (27011, 1), (163700279160878267, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_11, prime_sixtyFourBJ_17, prime_sixtyFourBJ_47, prime_sixtyFourBJ_59, prime_sixtyFourBJ_27011, prime_sixtyFourBJ_163700279160878267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142472 : Nat.totient 75665080582580626720727142472 = 37786275853720576106308770240 := by
  rw [← show ((([(2, 3), (1063, 1), (3541, 1), (2512732868223835218323, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_1063, prime_sixtyFourBJ_3541, prime_sixtyFourBJ_2512732868223835218323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142473 : Nat.totient 75665080582580626720727142473 = 75665080581977841007750464768 := by
  rw [← show ((([(125525696297, 1), (602785587450981409, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_125525696297, prime_sixtyFourBJ_602785587450981409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142474 : Nat.totient 75665080582580626720727142474 = 21613985926382016586170213840 := by
  rw [← show ((([(2, 1), (3, 4), (7, 2), (4691, 1), (2031977858852188094503, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_7, prime_sixtyFourBJ_4691, prime_sixtyFourBJ_2031977858852188094503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142475 : Nat.totient 75665080582580626720727142475 = 60530923363561700756349978720 := by
  rw [← show ((([(5, 2), (53047, 1), (57055125140031011533717, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_5, prime_sixtyFourBJ_53047, prime_sixtyFourBJ_57055125140031011533717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142476 : Nat.totient 75665080582580626720727142476 = 37204513138990549616857077888 := by
  rw [← show ((([(2, 2), (107, 1), (137, 1), (42139, 1), (30622943819165669219, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_107, prime_sixtyFourBJ_137, prime_sixtyFourBJ_42139, prime_sixtyFourBJ_30622943819165669219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142477 : Nat.totient 75665080582580626720727142477 = 50376377267910197640751280000 := by
  rw [← show ((([(3, 1), (1481, 1), (1811, 1), (9851, 1), (954597771786408599, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_1481, prime_sixtyFourBJ_1811, prime_sixtyFourBJ_9851, prime_sixtyFourBJ_954597771786408599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142478 : Nat.totient 75665080582580626720727142478 = 36959337761475385545820876800 := by
  rw [← show ((([(2, 1), (61, 1), (149, 1), (13217, 1), (81563, 1), (3861209077232581, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_61, prime_sixtyFourBJ_149, prime_sixtyFourBJ_13217, prime_sixtyFourBJ_81563, prime_sixtyFourBJ_3861209077232581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142479 : Nat.totient 75665080582580626720727142479 = 69399819133067581196080944096 := by
  rw [← show ((([(13, 1), (157, 1), (37072552955698494228675719, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_13, prime_sixtyFourBJ_157, prime_sixtyFourBJ_37072552955698494228675719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142480 : Nat.totient 75665080582580626720727142480 = 19115386531847838929649254400 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (19, 1), (9767977, 1), (66092629, 1), (25702359901, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_5, prime_sixtyFourBJ_19, prime_sixtyFourBJ_9767977, prime_sixtyFourBJ_66092629, prime_sixtyFourBJ_25702359901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142481 : Nat.totient 75665080582580626720727142481 = 64837550074699395626869905648 := by
  rw [← show ((([(7, 1), (3557, 1), (3038880299714069911270619, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_7, prime_sixtyFourBJ_3557, prime_sixtyFourBJ_3038880299714069911270619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142482 : Nat.totient 75665080582580626720727142482 = 34102713803206131608843666880 := by
  rw [← show ((([(2, 1), (11, 1), (127, 1), (1733, 1), (16162739, 1), (966842147993819, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_11, prime_sixtyFourBJ_127, prime_sixtyFourBJ_1733, prime_sixtyFourBJ_16162739, prime_sixtyFourBJ_966842147993819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142483 : Nat.totient 75665080582580626720727142483 = 50443384660801711482146918400 := by
  rw [← show ((([(3, 2), (21122939, 1), (10405850401, 1), (38249086433, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_21122939, prime_sixtyFourBJ_10405850401, prime_sixtyFourBJ_38249086433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142484 : Nat.totient 75665080582580626720727142484 = 36527941656784405014108521600 := by
  rw [← show ((([(2, 2), (29, 1), (1291931, 1), (7034989391, 1), (71768644469, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_29, prime_sixtyFourBJ_1291931, prime_sixtyFourBJ_7034989391, prime_sixtyFourBJ_71768644469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142485 : Nat.totient 75665080582580626720727142485 = 57625461237037165312632422400 := by
  rw [← show ((([(5, 1), (23, 1), (211, 1), (239521, 1), (460813, 1), (28251849536513, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_5, prime_sixtyFourBJ_23, prime_sixtyFourBJ_211, prime_sixtyFourBJ_239521, prime_sixtyFourBJ_460813, prime_sixtyFourBJ_28251849536513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142486 : Nat.totient 75665080582580626720727142486 = 24606530270757927388854355200 := by
  rw [← show ((([(2, 1), (3, 1), (41, 1), (307581628384474092360679441, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_41, prime_sixtyFourBJ_307581628384474092360679441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142487 : Nat.totient 75665080582580626720727142487 = 75536055618016555366907773792 := by
  rw [← show ((([(587, 1), (617453, 1), (58120199, 1), (3591917887583, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_587, prime_sixtyFourBJ_617453, prime_sixtyFourBJ_58120199, prime_sixtyFourBJ_3591917887583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142488 : Nat.totient 75665080582580626720727142488 = 30520368280931682179209605120 := by
  rw [← show ((([(2, 3), (7, 1), (17, 1), (85390729, 1), (930781685472841061, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_7, prime_sixtyFourBJ_17, prime_sixtyFourBJ_85390729, prime_sixtyFourBJ_930781685472841061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142489 : Nat.totient 75665080582580626720727142489 = 49990247396437103534784994560 := by
  rw [← show ((([(3, 1), (131, 1), (877, 1), (4547, 1), (928620083, 1), (51992455549, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_131, prime_sixtyFourBJ_877, prime_sixtyFourBJ_4547, prime_sixtyFourBJ_928620083, prime_sixtyFourBJ_51992455549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142490 : Nat.totient 75665080582580626720727142490 = 30266032212764257299303379456 := by
  rw [← show ((([(2, 1), (5, 1), (1493291993, 1), (5066998345753577393, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_1493291993, prime_sixtyFourBJ_5066998345753577393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142491 : Nat.totient 75665080582580626720727142491 = 73702143549791344948906671840 := by
  rw [← show ((([(53, 1), (271, 1), (283, 1), (18615036963738696164179, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_53, prime_sixtyFourBJ_271, prime_sixtyFourBJ_283, prime_sixtyFourBJ_18615036963738696164179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142492 : Nat.totient 75665080582580626720727142492 = 22826394324898368935442776064 := by
  rw [← show ((([(2, 2), (3, 2), (13, 2), (67, 1), (337, 1), (577, 1), (209702833, 1), (4552201517, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_13, prime_sixtyFourBJ_67, prime_sixtyFourBJ_337, prime_sixtyFourBJ_577, prime_sixtyFourBJ_209702833, prime_sixtyFourBJ_4552201517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142493 : Nat.totient 75665080582580626720727142493 = 68105383062628826931347562000 := by
  rw [← show ((([(11, 1), (101, 1), (68105383062628826931347563, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_11, prime_sixtyFourBJ_101, prime_sixtyFourBJ_68105383062628826931347563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142494 : Nat.totient 75665080582580626720727142494 = 37832540291290313360363571246 := by
  rw [← show ((([(2, 1), (37832540291290313360363571247, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_37832540291290313360363571247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142495 : Nat.totient 75665080582580626720727142495 = 34494426184305676838071173120 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (379, 1), (8513, 1), (5181217, 1), (43107473975941, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_3, prime_sixtyFourBJ_5, prime_sixtyFourBJ_7, prime_sixtyFourBJ_379, prime_sixtyFourBJ_8513, prime_sixtyFourBJ_5181217, prime_sixtyFourBJ_43107473975941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142496 : Nat.totient 75665080582580626720727142496 = 37832540291290313360363571232 := by
  rw [← show ((([(2, 5), (2364533768205644585022723203, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_2364533768205644585022723203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142497 : Nat.totient 75665080582580626720727142497 = 75594740555575322614721337984 := by
  rw [← show ((([(1109, 1), (35797, 1), (1905975531914486003689, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_1109, prime_sixtyFourBJ_35797, prime_sixtyFourBJ_1905975531914486003689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142498 : Nat.totient 75665080582580626720727142498 = 25221577067213868971173397216 := by
  rw [← show ((([(2, 1), (3, 1), (216569, 1), (58230156503301200941907, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_3, prime_sixtyFourBJ_216569, prime_sixtyFourBJ_58230156503301200941907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142499 : Nat.totient 75665080582580626720727142499 = 69343922486838016164418951680 := by
  rw [← show ((([(19, 1), (31, 1), (2633, 1), (741599, 1), (65790048948804073, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_19, prime_sixtyFourBJ_31, prime_sixtyFourBJ_2633, prime_sixtyFourBJ_741599, prime_sixtyFourBJ_65790048948804073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFourBJ_75665080582580626720727142500 : Nat.totient 75665080582580626720727142500 = 30150952262564447453734356000 := by
  rw [← show ((([(2, 2), (5, 4), (263, 1), (115079970467803234556239, 1)] : List FactorBlock).map factorBlockValue).prod) = 75665080582580626720727142500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFourBJ_2, prime_sixtyFourBJ_5, prime_sixtyFourBJ_263, prime_sixtyFourBJ_115079970467803234556239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyFourBJ : certifiedKill 1 75665080582580626720727142399 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyFourBJ_75665080582580626720727142400, phi_sixtyFourBJ_75665080582580626720727142401, phi_sixtyFourBJ_75665080582580626720727142402,
    phi_sixtyFourBJ_75665080582580626720727142403, phi_sixtyFourBJ_75665080582580626720727142404, phi_sixtyFourBJ_75665080582580626720727142405,
    phi_sixtyFourBJ_75665080582580626720727142406, phi_sixtyFourBJ_75665080582580626720727142407, phi_sixtyFourBJ_75665080582580626720727142408,
    phi_sixtyFourBJ_75665080582580626720727142409, phi_sixtyFourBJ_75665080582580626720727142410, phi_sixtyFourBJ_75665080582580626720727142411,
    phi_sixtyFourBJ_75665080582580626720727142412, phi_sixtyFourBJ_75665080582580626720727142413, phi_sixtyFourBJ_75665080582580626720727142414,
    phi_sixtyFourBJ_75665080582580626720727142415, phi_sixtyFourBJ_75665080582580626720727142416, phi_sixtyFourBJ_75665080582580626720727142417,
    phi_sixtyFourBJ_75665080582580626720727142418, phi_sixtyFourBJ_75665080582580626720727142419, phi_sixtyFourBJ_75665080582580626720727142420,
    phi_sixtyFourBJ_75665080582580626720727142421, phi_sixtyFourBJ_75665080582580626720727142422, phi_sixtyFourBJ_75665080582580626720727142423,
    phi_sixtyFourBJ_75665080582580626720727142424, phi_sixtyFourBJ_75665080582580626720727142425, phi_sixtyFourBJ_75665080582580626720727142426,
    phi_sixtyFourBJ_75665080582580626720727142427, phi_sixtyFourBJ_75665080582580626720727142428, phi_sixtyFourBJ_75665080582580626720727142429,
    phi_sixtyFourBJ_75665080582580626720727142430, phi_sixtyFourBJ_75665080582580626720727142431, phi_sixtyFourBJ_75665080582580626720727142432,
    phi_sixtyFourBJ_75665080582580626720727142433, phi_sixtyFourBJ_75665080582580626720727142434, phi_sixtyFourBJ_75665080582580626720727142435,
    phi_sixtyFourBJ_75665080582580626720727142436, phi_sixtyFourBJ_75665080582580626720727142437, phi_sixtyFourBJ_75665080582580626720727142438,
    phi_sixtyFourBJ_75665080582580626720727142439, phi_sixtyFourBJ_75665080582580626720727142440, phi_sixtyFourBJ_75665080582580626720727142441,
    phi_sixtyFourBJ_75665080582580626720727142442, phi_sixtyFourBJ_75665080582580626720727142443, phi_sixtyFourBJ_75665080582580626720727142444,
    phi_sixtyFourBJ_75665080582580626720727142445, phi_sixtyFourBJ_75665080582580626720727142446, phi_sixtyFourBJ_75665080582580626720727142447,
    phi_sixtyFourBJ_75665080582580626720727142448, phi_sixtyFourBJ_75665080582580626720727142449, phi_sixtyFourBJ_75665080582580626720727142450,
    phi_sixtyFourBJ_75665080582580626720727142451, phi_sixtyFourBJ_75665080582580626720727142452, phi_sixtyFourBJ_75665080582580626720727142453,
    phi_sixtyFourBJ_75665080582580626720727142454, phi_sixtyFourBJ_75665080582580626720727142455, phi_sixtyFourBJ_75665080582580626720727142456,
    phi_sixtyFourBJ_75665080582580626720727142457, phi_sixtyFourBJ_75665080582580626720727142458, phi_sixtyFourBJ_75665080582580626720727142459,
    phi_sixtyFourBJ_75665080582580626720727142460, phi_sixtyFourBJ_75665080582580626720727142461, phi_sixtyFourBJ_75665080582580626720727142462,
    phi_sixtyFourBJ_75665080582580626720727142463, phi_sixtyFourBJ_75665080582580626720727142464, phi_sixtyFourBJ_75665080582580626720727142465,
    phi_sixtyFourBJ_75665080582580626720727142466, phi_sixtyFourBJ_75665080582580626720727142467, phi_sixtyFourBJ_75665080582580626720727142468,
    phi_sixtyFourBJ_75665080582580626720727142469, phi_sixtyFourBJ_75665080582580626720727142470, phi_sixtyFourBJ_75665080582580626720727142471,
    phi_sixtyFourBJ_75665080582580626720727142472, phi_sixtyFourBJ_75665080582580626720727142473, phi_sixtyFourBJ_75665080582580626720727142474,
    phi_sixtyFourBJ_75665080582580626720727142475, phi_sixtyFourBJ_75665080582580626720727142476, phi_sixtyFourBJ_75665080582580626720727142477,
    phi_sixtyFourBJ_75665080582580626720727142478, phi_sixtyFourBJ_75665080582580626720727142479, phi_sixtyFourBJ_75665080582580626720727142480,
    phi_sixtyFourBJ_75665080582580626720727142481, phi_sixtyFourBJ_75665080582580626720727142482, phi_sixtyFourBJ_75665080582580626720727142483,
    phi_sixtyFourBJ_75665080582580626720727142484, phi_sixtyFourBJ_75665080582580626720727142485, phi_sixtyFourBJ_75665080582580626720727142486,
    phi_sixtyFourBJ_75665080582580626720727142487, phi_sixtyFourBJ_75665080582580626720727142488, phi_sixtyFourBJ_75665080582580626720727142489,
    phi_sixtyFourBJ_75665080582580626720727142490, phi_sixtyFourBJ_75665080582580626720727142491, phi_sixtyFourBJ_75665080582580626720727142492,
    phi_sixtyFourBJ_75665080582580626720727142493, phi_sixtyFourBJ_75665080582580626720727142494, phi_sixtyFourBJ_75665080582580626720727142495,
    phi_sixtyFourBJ_75665080582580626720727142496, phi_sixtyFourBJ_75665080582580626720727142497, phi_sixtyFourBJ_75665080582580626720727142498,
    phi_sixtyFourBJ_75665080582580626720727142499, phi_sixtyFourBJ_75665080582580626720727142500]

end TotientTailPeriodKiller
end Erdos249257
