import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtyOneACFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyOneACFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyOneACFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyOneACFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyOneACFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyOneACFastPow a n * thirtyOneACFastPow a n * a
        else thirtyOneACFastPow a n * thirtyOneACFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyOneAC_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtyOneAC_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtyOneAC_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtyOneAC_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtyOneAC_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtyOneAC_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtyOneAC_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtyOneAC_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtyOneAC_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtyOneAC_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtyOneAC_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtyOneAC_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtyOneAC_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtyOneAC_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtyOneAC_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtyOneAC_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtyOneAC_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtyOneAC_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtyOneAC_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtyOneAC_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtyOneAC_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtyOneAC_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtyOneAC_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtyOneAC_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtyOneAC_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtyOneAC_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtyOneAC_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtyOneAC_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtyOneAC_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtyOneAC_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtyOneAC_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtyOneAC_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtyOneAC_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtyOneAC_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtyOneAC_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtyOneAC_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirtyOneAC_157 : Nat.Prime 157 := by norm_num
private theorem prime_thirtyOneAC_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtyOneAC_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirtyOneAC_179 : Nat.Prime 179 := by norm_num
private theorem prime_thirtyOneAC_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirtyOneAC_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtyOneAC_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirtyOneAC_197 : Nat.Prime 197 := by norm_num
private theorem prime_thirtyOneAC_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirtyOneAC_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtyOneAC_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirtyOneAC_233 : Nat.Prime 233 := by norm_num
private theorem prime_thirtyOneAC_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirtyOneAC_241 : Nat.Prime 241 := by norm_num
private theorem prime_thirtyOneAC_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirtyOneAC_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtyOneAC_263 : Nat.Prime 263 := by norm_num
private theorem prime_thirtyOneAC_269 : Nat.Prime 269 := by norm_num
private theorem prime_thirtyOneAC_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtyOneAC_277 : Nat.Prime 277 := by norm_num
private theorem prime_thirtyOneAC_281 : Nat.Prime 281 := by norm_num
private theorem prime_thirtyOneAC_283 : Nat.Prime 283 := by norm_num
private theorem prime_thirtyOneAC_293 : Nat.Prime 293 := by norm_num
private theorem prime_thirtyOneAC_307 : Nat.Prime 307 := by norm_num
private theorem prime_thirtyOneAC_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirtyOneAC_313 : Nat.Prime 313 := by norm_num
private theorem prime_thirtyOneAC_317 : Nat.Prime 317 := by norm_num
private theorem prime_thirtyOneAC_331 : Nat.Prime 331 := by norm_num
private theorem prime_thirtyOneAC_337 : Nat.Prime 337 := by norm_num
private theorem prime_thirtyOneAC_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtyOneAC_359 : Nat.Prime 359 := by norm_num
private theorem prime_thirtyOneAC_367 : Nat.Prime 367 := by norm_num
private theorem prime_thirtyOneAC_389 : Nat.Prime 389 := by norm_num
private theorem prime_thirtyOneAC_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtyOneAC_419 : Nat.Prime 419 := by norm_num
private theorem prime_thirtyOneAC_433 : Nat.Prime 433 := by norm_num
private theorem prime_thirtyOneAC_449 : Nat.Prime 449 := by norm_num
private theorem prime_thirtyOneAC_457 : Nat.Prime 457 := by norm_num
private theorem prime_thirtyOneAC_467 : Nat.Prime 467 := by norm_num
private theorem prime_thirtyOneAC_479 : Nat.Prime 479 := by norm_num
private theorem prime_thirtyOneAC_499 : Nat.Prime 499 := by norm_num
private theorem prime_thirtyOneAC_521 : Nat.Prime 521 := by norm_num
private theorem prime_thirtyOneAC_523 : Nat.Prime 523 := by norm_num
private theorem prime_thirtyOneAC_547 : Nat.Prime 547 := by norm_num
private theorem prime_thirtyOneAC_557 : Nat.Prime 557 := by norm_num
private theorem prime_thirtyOneAC_563 : Nat.Prime 563 := by norm_num
private theorem prime_thirtyOneAC_569 : Nat.Prime 569 := by norm_num
private theorem prime_thirtyOneAC_571 : Nat.Prime 571 := by norm_num
private theorem prime_thirtyOneAC_577 : Nat.Prime 577 := by norm_num
private theorem prime_thirtyOneAC_587 : Nat.Prime 587 := by norm_num
private theorem prime_thirtyOneAC_619 : Nat.Prime 619 := by norm_num
private theorem prime_thirtyOneAC_631 : Nat.Prime 631 := by norm_num
private theorem prime_thirtyOneAC_647 : Nat.Prime 647 := by norm_num
private theorem prime_thirtyOneAC_661 : Nat.Prime 661 := by norm_num
private theorem prime_thirtyOneAC_673 : Nat.Prime 673 := by norm_num
private theorem prime_thirtyOneAC_683 : Nat.Prime 683 := by norm_num
private theorem prime_thirtyOneAC_727 : Nat.Prime 727 := by norm_num
private theorem prime_thirtyOneAC_811 : Nat.Prime 811 := by norm_num
private theorem prime_thirtyOneAC_821 : Nat.Prime 821 := by norm_num
private theorem prime_thirtyOneAC_829 : Nat.Prime 829 := by norm_num
private theorem prime_thirtyOneAC_853 : Nat.Prime 853 := by norm_num
private theorem prime_thirtyOneAC_857 : Nat.Prime 857 := by norm_num
private theorem prime_thirtyOneAC_859 : Nat.Prime 859 := by norm_num
private theorem prime_thirtyOneAC_863 : Nat.Prime 863 := by norm_num
private theorem prime_thirtyOneAC_877 : Nat.Prime 877 := by norm_num
private theorem prime_thirtyOneAC_887 : Nat.Prime 887 := by norm_num
private theorem prime_thirtyOneAC_907 : Nat.Prime 907 := by norm_num
private theorem prime_thirtyOneAC_941 : Nat.Prime 941 := by norm_num
private theorem prime_thirtyOneAC_991 : Nat.Prime 991 := by norm_num
private theorem prime_thirtyOneAC_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_thirtyOneAC_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_thirtyOneAC_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_thirtyOneAC_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_thirtyOneAC_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_thirtyOneAC_1237 : Nat.Prime 1237 := by norm_num
private theorem prime_thirtyOneAC_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_thirtyOneAC_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_thirtyOneAC_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_thirtyOneAC_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_thirtyOneAC_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_thirtyOneAC_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_thirtyOneAC_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_thirtyOneAC_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_thirtyOneAC_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_thirtyOneAC_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_thirtyOneAC_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_thirtyOneAC_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_thirtyOneAC_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_thirtyOneAC_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_thirtyOneAC_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_thirtyOneAC_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_thirtyOneAC_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_thirtyOneAC_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_thirtyOneAC_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_thirtyOneAC_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_thirtyOneAC_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_thirtyOneAC_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_thirtyOneAC_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_thirtyOneAC_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_thirtyOneAC_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_thirtyOneAC_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtyOneAC_2549 : Nat.Prime 2549 := by norm_num
private theorem prime_thirtyOneAC_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_thirtyOneAC_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_thirtyOneAC_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_thirtyOneAC_2953 : Nat.Prime 2953 := by norm_num
private theorem prime_thirtyOneAC_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_thirtyOneAC_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_thirtyOneAC_3313 : Nat.Prime 3313 := by norm_num
private theorem prime_thirtyOneAC_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_thirtyOneAC_3529 : Nat.Prime 3529 := by norm_num
private theorem prime_thirtyOneAC_3631 : Nat.Prime 3631 := by norm_num
private theorem prime_thirtyOneAC_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_thirtyOneAC_3863 : Nat.Prime 3863 := by norm_num
private theorem prime_thirtyOneAC_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_thirtyOneAC_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_thirtyOneAC_4073 : Nat.Prime 4073 := by norm_num
private theorem prime_thirtyOneAC_4243 : Nat.Prime 4243 := by norm_num
private theorem prime_thirtyOneAC_4297 : Nat.Prime 4297 := by norm_num
private theorem prime_thirtyOneAC_4409 : Nat.Prime 4409 := by norm_num
private theorem prime_thirtyOneAC_4547 : Nat.Prime 4547 := by norm_num
private theorem prime_thirtyOneAC_4651 : Nat.Prime 4651 := by norm_num
private theorem prime_thirtyOneAC_4721 : Nat.Prime 4721 := by norm_num
private theorem prime_thirtyOneAC_4723 : Nat.Prime 4723 := by norm_num
private theorem prime_thirtyOneAC_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_thirtyOneAC_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_thirtyOneAC_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtyOneAC_5107 : Nat.Prime 5107 := by norm_num
private theorem prime_thirtyOneAC_5323 : Nat.Prime 5323 := by norm_num
private theorem prime_thirtyOneAC_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_thirtyOneAC_5521 : Nat.Prime 5521 := by norm_num
private theorem prime_thirtyOneAC_5807 : Nat.Prime 5807 := by norm_num
private theorem prime_thirtyOneAC_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_thirtyOneAC_6053 : Nat.Prime 6053 := by norm_num
private theorem prime_thirtyOneAC_6073 : Nat.Prime 6073 := by norm_num
private theorem prime_thirtyOneAC_6089 : Nat.Prime 6089 := by norm_num
private theorem prime_thirtyOneAC_6197 : Nat.Prime 6197 := by norm_num
private theorem prime_thirtyOneAC_6257 : Nat.Prime 6257 := by norm_num
private theorem prime_thirtyOneAC_6263 : Nat.Prime 6263 := by norm_num
private theorem prime_thirtyOneAC_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_thirtyOneAC_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtyOneAC_6959 : Nat.Prime 6959 := by norm_num
private theorem prime_thirtyOneAC_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_thirtyOneAC_7213 : Nat.Prime 7213 := by norm_num
private theorem prime_thirtyOneAC_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_thirtyOneAC_7573 : Nat.Prime 7573 := by norm_num
private theorem prime_thirtyOneAC_7907 : Nat.Prime 7907 := by norm_num
private theorem prime_thirtyOneAC_8081 : Nat.Prime 8081 := by norm_num
private theorem prime_thirtyOneAC_8461 : Nat.Prime 8461 := by norm_num
private theorem prime_thirtyOneAC_9241 : Nat.Prime 9241 := by norm_num
private theorem prime_thirtyOneAC_9349 : Nat.Prime 9349 := by norm_num
private theorem prime_thirtyOneAC_9931 : Nat.Prime 9931 := by norm_num
private theorem prime_thirtyOneAC_9949 : Nat.Prime 9949 := by norm_num
private theorem prime_thirtyOneAC_9973 : Nat.Prime 9973 := by norm_num
private theorem prime_thirtyOneAC_10193 : Nat.Prime 10193 := by norm_num
private theorem prime_thirtyOneAC_10333 : Nat.Prime 10333 := by norm_num
private theorem prime_thirtyOneAC_10429 : Nat.Prime 10429 := by norm_num
private theorem prime_thirtyOneAC_10453 : Nat.Prime 10453 := by norm_num
private theorem prime_thirtyOneAC_10529 : Nat.Prime 10529 := by norm_num
private theorem prime_thirtyOneAC_10973 : Nat.Prime 10973 := by norm_num
private theorem prime_thirtyOneAC_10987 : Nat.Prime 10987 := by norm_num
private theorem prime_thirtyOneAC_11813 : Nat.Prime 11813 := by norm_num
private theorem prime_thirtyOneAC_11863 : Nat.Prime 11863 := by norm_num
private theorem prime_thirtyOneAC_11933 : Nat.Prime 11933 := by norm_num
private theorem prime_thirtyOneAC_12689 : Nat.Prime 12689 := by norm_num
private theorem prime_thirtyOneAC_12757 : Nat.Prime 12757 := by norm_num
private theorem prime_thirtyOneAC_13687 : Nat.Prime 13687 := by norm_num
private theorem prime_thirtyOneAC_13829 : Nat.Prime 13829 := by norm_num
private theorem prime_thirtyOneAC_14303 : Nat.Prime 14303 := by norm_num
private theorem prime_thirtyOneAC_14437 : Nat.Prime 14437 := by norm_num
private theorem prime_thirtyOneAC_14827 : Nat.Prime 14827 := by norm_num
private theorem prime_thirtyOneAC_15647 : Nat.Prime 15647 := by norm_num
private theorem prime_thirtyOneAC_15937 : Nat.Prime 15937 := by norm_num
private theorem prime_thirtyOneAC_16033 : Nat.Prime 16033 := by norm_num
private theorem prime_thirtyOneAC_16267 : Nat.Prime 16267 := by norm_num
private theorem prime_thirtyOneAC_16963 : Nat.Prime 16963 := by norm_num
private theorem prime_thirtyOneAC_16979 : Nat.Prime 16979 := by norm_num
private theorem prime_thirtyOneAC_18329 : Nat.Prime 18329 := by norm_num
private theorem prime_thirtyOneAC_19301 : Nat.Prime 19301 := by norm_num
private theorem prime_thirtyOneAC_19373 : Nat.Prime 19373 := by norm_num
private theorem prime_thirtyOneAC_19471 : Nat.Prime 19471 := by norm_num
private theorem prime_thirtyOneAC_19739 : Nat.Prime 19739 := by norm_num
private theorem prime_thirtyOneAC_20959 : Nat.Prime 20959 := by norm_num
private theorem prime_thirtyOneAC_22093 : Nat.Prime 22093 := by norm_num
private theorem prime_thirtyOneAC_22129 : Nat.Prime 22129 := by norm_num
private theorem prime_thirtyOneAC_22619 : Nat.Prime 22619 := by norm_num
private theorem prime_thirtyOneAC_22807 : Nat.Prime 22807 := by norm_num
private theorem prime_thirtyOneAC_23917 : Nat.Prime 23917 := by norm_num
private theorem prime_thirtyOneAC_25031 : Nat.Prime 25031 := by norm_num
private theorem prime_thirtyOneAC_25667 : Nat.Prime 25667 := by norm_num
private theorem prime_thirtyOneAC_26029 : Nat.Prime 26029 := by norm_num
private theorem prime_thirtyOneAC_26161 : Nat.Prime 26161 := by norm_num
private theorem prime_thirtyOneAC_26783 : Nat.Prime 26783 := by norm_num
private theorem prime_thirtyOneAC_31469 : Nat.Prime 31469 := by norm_num
private theorem prime_thirtyOneAC_32561 : Nat.Prime 32561 := by norm_num
private theorem prime_thirtyOneAC_33589 : Nat.Prime 33589 := by norm_num
private theorem prime_thirtyOneAC_33647 : Nat.Prime 33647 := by norm_num
private theorem prime_thirtyOneAC_33713 : Nat.Prime 33713 := by norm_num
private theorem prime_thirtyOneAC_34613 : Nat.Prime 34613 := by norm_num
private theorem prime_thirtyOneAC_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtyOneAC_35521 : Nat.Prime 35521 := by norm_num
private theorem prime_thirtyOneAC_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtyOneAC_37493 : Nat.Prime 37493 := by norm_num
private theorem prime_thirtyOneAC_38239 : Nat.Prime 38239 := by norm_num
private theorem prime_thirtyOneAC_39409 : Nat.Prime 39409 := by norm_num
private theorem prime_thirtyOneAC_40763 : Nat.Prime 40763 := by norm_num
private theorem prime_thirtyOneAC_42227 : Nat.Prime 42227 := by norm_num
private theorem prime_thirtyOneAC_43649 : Nat.Prime 43649 := by norm_num
private theorem prime_thirtyOneAC_46307 : Nat.Prime 46307 := by norm_num
private theorem prime_thirtyOneAC_46703 : Nat.Prime 46703 := by norm_num
private theorem prime_thirtyOneAC_46747 : Nat.Prime 46747 := by norm_num
private theorem prime_thirtyOneAC_51071 : Nat.Prime 51071 := by norm_num
private theorem prime_thirtyOneAC_52489 : Nat.Prime 52489 := by norm_num
private theorem prime_thirtyOneAC_53017 : Nat.Prime 53017 := by norm_num
private theorem prime_thirtyOneAC_53717 : Nat.Prime 53717 := by norm_num
private theorem prime_thirtyOneAC_57427 : Nat.Prime 57427 := by norm_num
private theorem prime_thirtyOneAC_57559 : Nat.Prime 57559 := by norm_num
private theorem prime_thirtyOneAC_59083 : Nat.Prime 59083 := by norm_num
private theorem prime_thirtyOneAC_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtyOneAC_63841 : Nat.Prime 63841 := by norm_num
private theorem prime_thirtyOneAC_65539 : Nat.Prime 65539 := by norm_num
private theorem prime_thirtyOneAC_65699 : Nat.Prime 65699 := by norm_num
private theorem prime_thirtyOneAC_69539 : Nat.Prime 69539 := by norm_num
private theorem prime_thirtyOneAC_71473 : Nat.Prime 71473 := by norm_num
private theorem prime_thirtyOneAC_74713 : Nat.Prime 74713 := by norm_num
private theorem prime_thirtyOneAC_77491 : Nat.Prime 77491 := by norm_num
private theorem prime_thirtyOneAC_79039 : Nat.Prime 79039 := by norm_num
private theorem prime_thirtyOneAC_80233 : Nat.Prime 80233 := by norm_num
private theorem prime_thirtyOneAC_90071 : Nat.Prime 90071 := by norm_num
private theorem prime_thirtyOneAC_90281 : Nat.Prime 90281 := by norm_num
private theorem prime_thirtyOneAC_94433 : Nat.Prime 94433 := by norm_num
private theorem prime_thirtyOneAC_104677 : Nat.Prime 104677 := by norm_num
private theorem prime_thirtyOneAC_106649 : Nat.Prime 106649 := by norm_num
private theorem prime_thirtyOneAC_113341 : Nat.Prime 113341 := by norm_num
private theorem prime_thirtyOneAC_113647 : Nat.Prime 113647 := by norm_num
private theorem prime_thirtyOneAC_113777 : Nat.Prime 113777 := by norm_num
private theorem prime_thirtyOneAC_114451 : Nat.Prime 114451 := by norm_num
private theorem prime_thirtyOneAC_118277 : Nat.Prime 118277 := by norm_num
private theorem prime_thirtyOneAC_122069 : Nat.Prime 122069 := by norm_num
private theorem prime_thirtyOneAC_126013 : Nat.Prime 126013 := by norm_num
private theorem prime_thirtyOneAC_136261 : Nat.Prime 136261 := by norm_num
private theorem prime_thirtyOneAC_136463 : Nat.Prime 136463 := by norm_num
private theorem prime_thirtyOneAC_138637 : Nat.Prime 138637 := by norm_num
private theorem prime_thirtyOneAC_141731 : Nat.Prime 141731 := by norm_num
private theorem prime_thirtyOneAC_142573 : Nat.Prime 142573 := by norm_num
private theorem prime_thirtyOneAC_150881 : Nat.Prime 150881 := by norm_num
private theorem prime_thirtyOneAC_151537 : Nat.Prime 151537 := by norm_num
private theorem prime_thirtyOneAC_160087 : Nat.Prime 160087 := by norm_num
private theorem prime_thirtyOneAC_164809 : Nat.Prime 164809 := by norm_num
private theorem prime_thirtyOneAC_166021 : Nat.Prime 166021 := by norm_num
private theorem prime_thirtyOneAC_185707 : Nat.Prime 185707 := by norm_num
private theorem prime_thirtyOneAC_187433 : Nat.Prime 187433 := by norm_num
private theorem prime_thirtyOneAC_211093 : Nat.Prime 211093 := by norm_num
private theorem prime_thirtyOneAC_211727 : Nat.Prime 211727 := by norm_num
private theorem prime_thirtyOneAC_212437 : Nat.Prime 212437 := by norm_num
private theorem prime_thirtyOneAC_212873 : Nat.Prime 212873 := by norm_num
private theorem prime_thirtyOneAC_214673 : Nat.Prime 214673 := by norm_num
private theorem prime_thirtyOneAC_225217 : Nat.Prime 225217 := by norm_num
private theorem prime_thirtyOneAC_236209 : Nat.Prime 236209 := by norm_num
private theorem prime_thirtyOneAC_249133 : Nat.Prime 249133 := by norm_num
private theorem prime_thirtyOneAC_253133 : Nat.Prime 253133 := by norm_num
private theorem prime_thirtyOneAC_256307 : Nat.Prime 256307 := by norm_num
private theorem prime_thirtyOneAC_260747 : Nat.Prime 260747 := by norm_num
private theorem prime_thirtyOneAC_272039 : Nat.Prime 272039 := by norm_num
private theorem prime_thirtyOneAC_291829 : Nat.Prime 291829 := by norm_num
private theorem prime_thirtyOneAC_298049 : Nat.Prime 298049 := by norm_num
private theorem prime_thirtyOneAC_306533 : Nat.Prime 306533 := by norm_num
private theorem prime_thirtyOneAC_324391 : Nat.Prime 324391 := by norm_num
private theorem prime_thirtyOneAC_326101 : Nat.Prime 326101 := by norm_num
private theorem prime_thirtyOneAC_332921 : Nat.Prime 332921 := by norm_num
private theorem prime_thirtyOneAC_338389 : Nat.Prime 338389 := by norm_num
private theorem prime_thirtyOneAC_342101 : Nat.Prime 342101 := by norm_num
private theorem prime_thirtyOneAC_362407 : Nat.Prime 362407 := by norm_num
private theorem prime_thirtyOneAC_366517 : Nat.Prime 366517 := by norm_num
private theorem prime_thirtyOneAC_382661 : Nat.Prime 382661 := by norm_num
private theorem prime_thirtyOneAC_421831 : Nat.Prime 421831 := by norm_num
private theorem prime_thirtyOneAC_444449 : Nat.Prime 444449 := by norm_num
private theorem prime_thirtyOneAC_459167 : Nat.Prime 459167 := by norm_num
private theorem prime_thirtyOneAC_461093 : Nat.Prime 461093 := by norm_num
private theorem prime_thirtyOneAC_483697 : Nat.Prime 483697 := by norm_num
private theorem prime_thirtyOneAC_504299 : Nat.Prime 504299 := by norm_num
private theorem prime_thirtyOneAC_535609 : Nat.Prime 535609 := by norm_num
private theorem prime_thirtyOneAC_587551 : Nat.Prime 587551 := by norm_num
private theorem prime_thirtyOneAC_597539 : Nat.Prime 597539 := by norm_num
private theorem prime_thirtyOneAC_652811 : Nat.Prime 652811 := by norm_num
private theorem prime_thirtyOneAC_683731 : Nat.Prime 683731 := by norm_num
private theorem prime_thirtyOneAC_709271 : Nat.Prime 709271 := by norm_num
private theorem prime_thirtyOneAC_749923 : Nat.Prime 749923 := by norm_num
private theorem prime_thirtyOneAC_822229 : Nat.Prime 822229 := by norm_num
private theorem prime_thirtyOneAC_826069 : Nat.Prime 826069 := by norm_num
private theorem prime_thirtyOneAC_836747 : Nat.Prime 836747 := by norm_num
private theorem prime_thirtyOneAC_900773 : Nat.Prime 900773 := by norm_num
private theorem prime_thirtyOneAC_945809 : Nat.Prime 945809 := by norm_num
private theorem prime_thirtyOneAC_1049827 : Nat.Prime 1049827 := by norm_num
private theorem prime_thirtyOneAC_1053713 : Nat.Prime 1053713 := by norm_num
private theorem prime_thirtyOneAC_1175099 : Nat.Prime 1175099 := by norm_num
private theorem prime_thirtyOneAC_1289423 : Nat.Prime 1289423 := by norm_num
private theorem prime_thirtyOneAC_1302383 : Nat.Prime 1302383 := by norm_num
private theorem prime_thirtyOneAC_1412057 : Nat.Prime 1412057 := by norm_num
private theorem prime_thirtyOneAC_1434497 : Nat.Prime 1434497 := by norm_num
private theorem prime_thirtyOneAC_1703963 : Nat.Prime 1703963 := by norm_num
private theorem prime_thirtyOneAC_1790879 : Nat.Prime 1790879 := by norm_num
private theorem prime_thirtyOneAC_1890227 : Nat.Prime 1890227 := by norm_num
private theorem prime_thirtyOneAC_1908041 : Nat.Prime 1908041 := by norm_num
private theorem prime_thirtyOneAC_1954247 : Nat.Prime 1954247 := by norm_num
private theorem prime_thirtyOneAC_1962911 : Nat.Prime 1962911 := by norm_num
private theorem prime_thirtyOneAC_2076433 : Nat.Prime 2076433 := by norm_num
private theorem prime_thirtyOneAC_2089751 : Nat.Prime 2089751 := by norm_num
private theorem prime_thirtyOneAC_2106389 : Nat.Prime 2106389 := by norm_num
private theorem prime_thirtyOneAC_2322239 : Nat.Prime 2322239 := by norm_num
private theorem prime_thirtyOneAC_2448539 : Nat.Prime 2448539 := by norm_num
private theorem prime_thirtyOneAC_2684273 : Nat.Prime 2684273 := by norm_num
private theorem prime_thirtyOneAC_2709197 : Nat.Prime 2709197 := by norm_num
private theorem prime_thirtyOneAC_2909981 : Nat.Prime 2909981 := by norm_num
private theorem prime_thirtyOneAC_3060583 : Nat.Prime 3060583 := by norm_num
private theorem prime_thirtyOneAC_3083359 : Nat.Prime 3083359 := by norm_num
private theorem prime_thirtyOneAC_3096659 : Nat.Prime 3096659 := by norm_num
private theorem prime_thirtyOneAC_3129121 : Nat.Prime 3129121 := by norm_num
private theorem prime_thirtyOneAC_3217931 : Nat.Prime 3217931 := by norm_num
private theorem prime_thirtyOneAC_3317603 : Nat.Prime 3317603 := by norm_num
private theorem prime_thirtyOneAC_3459017 : Nat.Prime 3459017 := by norm_num
private theorem prime_thirtyOneAC_3580229 : Nat.Prime 3580229 := by norm_num
private theorem prime_thirtyOneAC_3884081 : Nat.Prime 3884081 := by norm_num
private theorem prime_thirtyOneAC_4120097 : Nat.Prime 4120097 := by norm_num
private theorem prime_thirtyOneAC_4540337 : Nat.Prime 4540337 := by norm_num
private theorem prime_thirtyOneAC_4604641 : Nat.Prime 4604641 := by norm_num
private theorem prime_thirtyOneAC_4649527 : Nat.Prime 4649527 := by norm_num
private theorem prime_thirtyOneAC_4655801 : Nat.Prime 4655801 := by norm_num
private theorem prime_thirtyOneAC_4671223 : Nat.Prime 4671223 := by norm_num
private theorem prime_thirtyOneAC_4754779 : Nat.Prime 4754779 := by norm_num
private theorem prime_thirtyOneAC_4760891 : Nat.Prime 4760891 := by norm_num
private theorem prime_thirtyOneAC_5446879 : Nat.Prime 5446879 := by norm_num
private theorem prime_thirtyOneAC_5453879 : Nat.Prime 5453879 := by norm_num
private theorem prime_thirtyOneAC_5480617 : Nat.Prime 5480617 := by norm_num
private theorem prime_thirtyOneAC_5498947 : Nat.Prime 5498947 := by norm_num
private theorem prime_thirtyOneAC_5884969 : Nat.Prime 5884969 := by norm_num
private theorem prime_thirtyOneAC_5894561 : Nat.Prime 5894561 := by norm_num
private theorem prime_thirtyOneAC_5949311 : Nat.Prime 5949311 := by norm_num
private theorem prime_thirtyOneAC_6169993 : Nat.Prime 6169993 := by norm_num
private theorem prime_thirtyOneAC_6415567 : Nat.Prime 6415567 := by norm_num
private theorem prime_thirtyOneAC_6655531 : Nat.Prime 6655531 := by norm_num
private theorem prime_thirtyOneAC_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtyOneAC_10217771 : Nat.Prime 10217771 := by norm_num
private theorem prime_thirtyOneAC_11003623 : Nat.Prime 11003623 := by norm_num
private theorem prime_thirtyOneAC_11068859 : Nat.Prime 11068859 := by norm_num
private theorem prime_thirtyOneAC_11269039 : Nat.Prime 11269039 := by norm_num
private theorem prime_thirtyOneAC_11549821 : Nat.Prime 11549821 := by norm_num
private theorem prime_thirtyOneAC_11553809 : Nat.Prime 11553809 := by norm_num
private theorem prime_thirtyOneAC_12902831 : Nat.Prime 12902831 := by norm_num
private theorem prime_thirtyOneAC_12998593 : Nat.Prime 12998593 := by norm_num
private theorem prime_thirtyOneAC_13247893 : Nat.Prime 13247893 := by norm_num
private theorem prime_thirtyOneAC_13613513 : Nat.Prime 13613513 := by norm_num
private theorem prime_thirtyOneAC_13952459 : Nat.Prime 13952459 := by norm_num
private theorem prime_thirtyOneAC_14593687 : Nat.Prime 14593687 := by norm_num
private theorem prime_thirtyOneAC_14653349 : Nat.Prime 14653349 := by norm_num
private theorem prime_thirtyOneAC_16528661 : Nat.Prime 16528661 := by norm_num
private theorem prime_thirtyOneAC_17690983 : Nat.Prime 17690983 := by norm_num
private theorem prime_thirtyOneAC_20545409 : Nat.Prime 20545409 := by norm_num
private theorem prime_thirtyOneAC_21026857 : Nat.Prime 21026857 := by norm_num
private theorem prime_thirtyOneAC_22079591 : Nat.Prime 22079591 := by norm_num
private theorem prime_thirtyOneAC_22137277 : Nat.Prime 22137277 := by norm_num
private theorem prime_thirtyOneAC_22486379 : Nat.Prime 22486379 := by norm_num
private theorem prime_thirtyOneAC_22857113 : Nat.Prime 22857113 := by norm_num
private theorem prime_thirtyOneAC_24265639 : Nat.Prime 24265639 := by norm_num

private theorem prime_thirtyOneAC_31190531 : Nat.Prime 31190531 := by
  apply lucas_primality 31190531 (6 : ZMod 31190531)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (19373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (19373, 1)] : List FactorBlock).map factorBlockValue).prod) = 31190531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_19373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31190531) ^ 15595265 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 31190531) ^ 6238106 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 31190531) ^ 4455790 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 31190531) ^ 1356110 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 31190531) ^ 1610 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_32135093 : Nat.Prime 32135093 := by
  apply lucas_primality 32135093 (2 : ZMod 32135093)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (37, 1), (19739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (37, 1), (19739, 1)] : List FactorBlock).map factorBlockValue).prod) = 32135093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_19739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32135093) ^ 16067546 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32135093) ^ 2921372 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32135093) ^ 868516 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32135093) ^ 1628 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_32174563 : Nat.Prime 32174563 := by
  apply lucas_primality 32174563 (2 : ZMod 32174563)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (23, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (23, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) = 32174563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_1753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32174563) ^ 16087281 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32174563) ^ 10724854 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32174563) ^ 4596366 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32174563) ^ 1693398 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32174563) ^ 1398894 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32174563) ^ 18354 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_32296087 : Nat.Prime 32296087 := by
  apply lucas_primality 32296087 (3 : ZMod 32296087)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (94433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (94433, 1)] : List FactorBlock).map factorBlockValue).prod) = 32296087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_94433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32296087) ^ 16148043 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 32296087) ^ 10765362 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 32296087) ^ 1699794 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 32296087) ^ 342 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_35343701 : Nat.Prime 35343701 := by
  apply lucas_primality 35343701 (2 : ZMod 35343701)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) = 35343701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_7213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35343701) ^ 17671850 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 35343701) ^ 7068740 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 35343701) ^ 5049100 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 35343701) ^ 4900 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_36356323 : Nat.Prime 36356323 := by
  apply lucas_primality 36356323 (3 : ZMod 36356323)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (103, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (103, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 36356323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_89
      · exact prime_thirtyOneAC_103
      · exact prime_thirtyOneAC_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36356323) ^ 18178161 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 36356323) ^ 12118774 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 36356323) ^ 408498 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 36356323) ^ 352974 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 36356323) ^ 55002 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_40417873 : Nat.Prime 40417873 := by
  apply lucas_primality 40417873 (7 : ZMod 40417873)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 2), (6959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 2), (6959, 1)] : List FactorBlock).map factorBlockValue).prod) = 40417873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_6959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 40417873) ^ 20208936 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 40417873) ^ 13472624 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 40417873) ^ 3674352 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 40417873) ^ 5808 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_40789657 : Nat.Prime 40789657 := by
  apply lucas_primality 40789657 (10 : ZMod 40789657)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (19, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (19, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) = 40789657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_3313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 40789657) ^ 20394828 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 40789657) ^ 13596552 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 40789657) ^ 2146824 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 40789657) ^ 12312 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_44944439 : Nat.Prime 44944439 := by
  apply lucas_primality 44944439 (7 : ZMod 44944439)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (23, 1), (12689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (23, 1), (12689, 1)] : List FactorBlock).map factorBlockValue).prod) = 44944439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_12689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 44944439) ^ 22472219 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 44944439) ^ 6420634 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 44944439) ^ 4085858 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 44944439) ^ 1954106 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 44944439) ^ 3542 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_53367757 : Nat.Prime 53367757 := by
  apply lucas_primality 53367757 (5 : ZMod 53367757)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (342101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (342101, 1)] : List FactorBlock).map factorBlockValue).prod) = 53367757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_342101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53367757) ^ 26683878 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 53367757) ^ 17789252 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 53367757) ^ 4105212 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 53367757) ^ 156 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_54050561 : Nat.Prime 54050561 := by
  apply lucas_primality 54050561 (3 : ZMod 54050561)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (42227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (42227, 1)] : List FactorBlock).map factorBlockValue).prod) = 54050561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_42227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 54050561) ^ 27025280 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 54050561) ^ 10810112 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 54050561) ^ 1280 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_55159861 : Nat.Prime 55159861 := by
  apply lucas_primality 55159861 (2 : ZMod 55159861)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61, 1), (2153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61, 1), (2153, 1)] : List FactorBlock).map factorBlockValue).prod) = 55159861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_61
      · exact prime_thirtyOneAC_2153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55159861) ^ 27579930 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55159861) ^ 18386620 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55159861) ^ 11031972 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55159861) ^ 7879980 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55159861) ^ 904260 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55159861) ^ 25620 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_56635027 : Nat.Prime 56635027 := by
  apply lucas_primality 56635027 (2 : ZMod 56635027)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (941, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (941, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) = 56635027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_941
      · exact prime_thirtyOneAC_1433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56635027) ^ 28317513 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 56635027) ^ 18878342 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 56635027) ^ 8090718 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 56635027) ^ 60186 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 56635027) ^ 39522 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_62880611 : Nat.Prime 62880611 := by
  apply lucas_primality 62880611 (6 : ZMod 62880611)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (483697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (483697, 1)] : List FactorBlock).map factorBlockValue).prod) = 62880611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_483697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 62880611) ^ 31440305 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62880611) ^ 12576122 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62880611) ^ 4836970 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62880611) ^ 130 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_63757147 : Nat.Prime 63757147 := by
  apply lucas_primality 63757147 (5 : ZMod 63757147)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (307, 1), (34613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (307, 1), (34613, 1)] : List FactorBlock).map factorBlockValue).prod) = 63757147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_307
      · exact prime_thirtyOneAC_34613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 63757147) ^ 31878573 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 63757147) ^ 21252382 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 63757147) ^ 207678 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 63757147) ^ 1842 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_64133863 : Nat.Prime 64133863 := by
  apply lucas_primality 64133863 (6 : ZMod 64133863)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (822229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (822229, 1)] : List FactorBlock).map factorBlockValue).prod) = 64133863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_822229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 64133863) ^ 32066931 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 64133863) ^ 21377954 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 64133863) ^ 4933374 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 64133863) ^ 78 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_67262959 : Nat.Prime 67262959 := by
  apply lucas_primality 67262959 (3 : ZMod 67262959)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (359, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (359, 1), (1487, 1)] : List FactorBlock).map factorBlockValue).prod) = 67262959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_359
      · exact prime_thirtyOneAC_1487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67262959) ^ 33631479 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 67262959) ^ 22420986 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 67262959) ^ 9608994 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 67262959) ^ 187362 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 67262959) ^ 45234 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_74311649 : Nat.Prime 74311649 := by
  apply lucas_primality 74311649 (3 : ZMod 74311649)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2322239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2322239, 1)] : List FactorBlock).map factorBlockValue).prod) = 74311649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_2322239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 74311649) ^ 37155824 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 74311649) ^ 32 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_74689913 : Nat.Prime 74689913 := by
  apply lucas_primality 74689913 (3 : ZMod 74689913)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (19, 1), (31, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (19, 1), (31, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 74689913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 74689913) ^ 37344956 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 74689913) ^ 6789992 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 74689913) ^ 3931048 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 74689913) ^ 2409352 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 74689913) ^ 570152 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_88550873 : Nat.Prime 88550873 := by
  apply lucas_primality 88550873 (3 : ZMod 88550873)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11068859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11068859, 1)] : List FactorBlock).map factorBlockValue).prod) = 88550873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11068859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 88550873) ^ 44275436 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 88550873) ^ 8 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_90825929 : Nat.Prime 90825929 := by
  apply lucas_primality 90825929 (3 : ZMod 90825929)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (597539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (597539, 1)] : List FactorBlock).map factorBlockValue).prod) = 90825929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_597539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 90825929) ^ 45412964 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 90825929) ^ 4780312 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 90825929) ^ 152 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_91438103 : Nat.Prime 91438103 := by
  apply lucas_primality 91438103 (5 : ZMod 91438103)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (225217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (225217, 1)] : List FactorBlock).map factorBlockValue).prod) = 91438103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_225217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 91438103) ^ 45719051 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 91438103) ^ 13062586 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 91438103) ^ 3153038 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 91438103) ^ 406 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_100525921 : Nat.Prime 100525921 := by
  apply lucas_primality 100525921 (13 : ZMod 100525921)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (11, 1), (79, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (11, 1), (79, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 100525921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_79
      · exact prime_thirtyOneAC_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 100525921) ^ 50262960 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 100525921) ^ 33508640 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 100525921) ^ 20105184 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 100525921) ^ 9138720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 100525921) ^ 1272480 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 100525921) ^ 417120 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_110502167 : Nat.Prime 110502167 := by
  apply lucas_primality 110502167 (5 : ZMod 110502167)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (31, 1), (77491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (31, 1), (77491, 1)] : List FactorBlock).map factorBlockValue).prod) = 110502167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_77491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 110502167) ^ 55251083 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 110502167) ^ 4804442 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 110502167) ^ 3564586 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 110502167) ^ 1426 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_113053243 : Nat.Prime 113053243 := by
  apply lucas_primality 113053243 (2 : ZMod 113053243)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1579, 1), (11933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1579, 1), (11933, 1)] : List FactorBlock).map factorBlockValue).prod) = 113053243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_1579
      · exact prime_thirtyOneAC_11933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113053243) ^ 56526621 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 113053243) ^ 37684414 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 113053243) ^ 71598 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 113053243) ^ 9474 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_114180713 : Nat.Prime 114180713 := by
  apply lucas_primality 114180713 (3 : ZMod 114180713)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (631, 1), (22619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (631, 1), (22619, 1)] : List FactorBlock).map factorBlockValue).prod) = 114180713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_631
      · exact prime_thirtyOneAC_22619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 114180713) ^ 57090356 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 114180713) ^ 180952 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 114180713) ^ 5048 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_115480207 : Nat.Prime 115480207 := by
  apply lucas_primality 115480207 (3 : ZMod 115480207)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6415567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6415567, 1)] : List FactorBlock).map factorBlockValue).prod) = 115480207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_6415567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 115480207) ^ 57740103 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 115480207) ^ 38493402 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 115480207) ^ 18 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_120216881 : Nat.Prime 120216881 := by
  apply lucas_primality 120216881 (3 : ZMod 120216881)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (214673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (214673, 1)] : List FactorBlock).map factorBlockValue).prod) = 120216881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_214673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120216881) ^ 60108440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 120216881) ^ 24043376 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 120216881) ^ 17173840 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 120216881) ^ 560 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_121230673 : Nat.Prime 121230673 := by
  apply lucas_primality 121230673 (5 : ZMod 121230673)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (29, 1), (47, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (29, 1), (47, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 121230673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 121230673) ^ 60615336 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 121230673) ^ 40410224 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 121230673) ^ 7131216 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 121230673) ^ 4180368 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 121230673) ^ 2579376 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 121230673) ^ 1112208 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_130574083 : Nat.Prime 130574083 := by
  apply lucas_primality 130574083 (2 : ZMod 130574083)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (223, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (223, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) = 130574083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_223
      · exact prime_thirtyOneAC_4243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 130574083) ^ 65287041 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 130574083) ^ 43524694 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 130574083) ^ 5677134 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 130574083) ^ 585534 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 130574083) ^ 30774 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_163159471 : Nat.Prime 163159471 := by
  apply lucas_primality 163159471 (3 : ZMod 163159471)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 3), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 3), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 163159471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 163159471) ^ 81579735 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 163159471) ^ 54386490 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 163159471) ^ 32631894 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 163159471) ^ 7093890 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 163159471) ^ 1095030 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_166550609 : Nat.Prime 166550609 := by
  apply lucas_primality 166550609 (3 : ZMod 166550609)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (212437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (212437, 1)] : List FactorBlock).map factorBlockValue).prod) = 166550609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_212437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 166550609) ^ 83275304 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 166550609) ^ 23792944 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 166550609) ^ 784 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_176071183 : Nat.Prime 176071183 := by
  apply lucas_primality 176071183 (3 : ZMod 176071183)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (73, 1), (57427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (73, 1), (57427, 1)] : List FactorBlock).map factorBlockValue).prod) = 176071183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_73
      · exact prime_thirtyOneAC_57427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 176071183) ^ 88035591 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 176071183) ^ 58690394 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 176071183) ^ 25153026 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 176071183) ^ 2411934 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 176071183) ^ 3066 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_181191887 : Nat.Prime 181191887 := by
  apply lucas_primality 181191887 (5 : ZMod 181191887)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (2448539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (2448539, 1)] : List FactorBlock).map factorBlockValue).prod) = 181191887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_2448539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 181191887) ^ 90595943 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 181191887) ^ 4897078 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 181191887) ^ 74 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_200216923 : Nat.Prime 200216923 := by
  apply lucas_primality 200216923 (3 : ZMod 200216923)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1962911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1962911, 1)] : List FactorBlock).map factorBlockValue).prod) = 200216923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_1962911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 200216923) ^ 100108461 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 200216923) ^ 66738974 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 200216923) ^ 11777466 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 200216923) ^ 102 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_204795599 : Nat.Prime 204795599 := by
  apply lucas_primality 204795599 (7 : ZMod 204795599)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (2089751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (2089751, 1)] : List FactorBlock).map factorBlockValue).prod) = 204795599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_2089751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 204795599) ^ 102397799 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 204795599) ^ 29256514 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 204795599) ^ 98 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_205990177 : Nat.Prime 205990177 := by
  apply lucas_primality 205990177 (5 : ZMod 205990177)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (306533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (306533, 1)] : List FactorBlock).map factorBlockValue).prod) = 205990177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_306533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 205990177) ^ 102995088 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 205990177) ^ 68663392 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 205990177) ^ 29427168 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 205990177) ^ 672 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_226540109 : Nat.Prime 226540109 := by
  apply lucas_primality 226540109 (2 : ZMod 226540109)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (56635027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (56635027, 1)] : List FactorBlock).map factorBlockValue).prod) = 226540109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_56635027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 226540109) ^ 113270054 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 226540109) ^ 4 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_234426737 : Nat.Prime 234426737 := by
  apply lucas_primality 234426737 (3 : ZMod 234426737)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (109, 1), (7907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (109, 1), (7907, 1)] : List FactorBlock).map factorBlockValue).prod) = 234426737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_109
      · exact prime_thirtyOneAC_7907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 234426737) ^ 117213368 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 234426737) ^ 13789808 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 234426737) ^ 2150704 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 234426737) ^ 29648 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_298958273 : Nat.Prime 298958273 := by
  apply lucas_primality 298958273 (3 : ZMod 298958273)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (4671223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (4671223, 1)] : List FactorBlock).map factorBlockValue).prod) = 298958273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_4671223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 298958273) ^ 149479136 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 298958273) ^ 64 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_311492647 : Nat.Prime 311492647 := by
  apply lucas_primality 311492647 (5 : ZMod 311492647)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (127, 1), (136261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (127, 1), (136261, 1)] : List FactorBlock).map factorBlockValue).prod) = 311492647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_127
      · exact prime_thirtyOneAC_136261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 311492647) ^ 155746323 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 311492647) ^ 103830882 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 311492647) ^ 2452698 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 311492647) ^ 2286 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_318933089 : Nat.Prime 318933089 := by
  apply lucas_primality 318933089 (3 : ZMod 318933089)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (23, 1), (22807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (23, 1), (22807, 1)] : List FactorBlock).map factorBlockValue).prod) = 318933089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_22807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 318933089) ^ 159466544 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 318933089) ^ 16785952 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 318933089) ^ 13866656 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 318933089) ^ 13984 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_328175231 : Nat.Prime 328175231 := by
  apply lucas_primality 328175231 (19 : ZMod 328175231)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (619, 1), (53017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (619, 1), (53017, 1)] : List FactorBlock).map factorBlockValue).prod) = 328175231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_619
      · exact prime_thirtyOneAC_53017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 328175231) ^ 164087615 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 328175231) ^ 65635046 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 328175231) ^ 530170 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 328175231) ^ 6190 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_330579971 : Nat.Prime 330579971 := by
  apply lucas_primality 330579971 (2 : ZMod 330579971)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 3), (31, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 3), (31, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) = 330579971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 330579971) ^ 165289985 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 330579971) ^ 66115994 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 330579971) ^ 47225710 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 330579971) ^ 10663870 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 330579971) ^ 106330 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_365160181 : Nat.Prime 365160181 := by
  apply lucas_primality 365160181 (18 : ZMod 365160181)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (79039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (79039, 1)] : List FactorBlock).map factorBlockValue).prod) = 365160181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_79039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 365160181) ^ 182580090 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (18 : ZMod 365160181) ^ 121720060 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (18 : ZMod 365160181) ^ 73032036 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (18 : ZMod 365160181) ^ 52165740 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (18 : ZMod 365160181) ^ 33196380 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (18 : ZMod 365160181) ^ 4620 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_371740913 : Nat.Prime 371740913 := by
  apply lucas_primality 371740913 (3 : ZMod 371740913)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4001, 1), (5807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4001, 1), (5807, 1)] : List FactorBlock).map factorBlockValue).prod) = 371740913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_4001
      · exact prime_thirtyOneAC_5807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 371740913) ^ 185870456 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 371740913) ^ 92912 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 371740913) ^ 64016 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_381643879 : Nat.Prime 381643879 := by
  apply lucas_primality 381643879 (6 : ZMod 381643879)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (826069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (826069, 1)] : List FactorBlock).map factorBlockValue).prod) = 381643879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_826069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 381643879) ^ 190821939 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 381643879) ^ 127214626 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 381643879) ^ 54520554 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 381643879) ^ 34694898 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 381643879) ^ 462 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_462152167 : Nat.Prime 462152167 := by
  apply lucas_primality 462152167 (11 : ZMod 462152167)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11003623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11003623, 1)] : List FactorBlock).map factorBlockValue).prod) = 462152167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11003623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 462152167) ^ 231076083 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 462152167) ^ 154050722 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 462152167) ^ 66021738 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 462152167) ^ 42 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_466780217 : Nat.Prime 466780217 := by
  apply lucas_primality 466780217 (3 : ZMod 466780217)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (23, 1), (362407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (23, 1), (362407, 1)] : List FactorBlock).map factorBlockValue).prod) = 466780217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_362407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 466780217) ^ 233390108 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 466780217) ^ 66682888 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 466780217) ^ 20294792 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 466780217) ^ 1288 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_622448929 : Nat.Prime 622448929 := by
  apply lucas_primality 622448929 (23 : ZMod 622448929)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (37, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (37, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) = 622448929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_19471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 622448929) ^ 311224464 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 622448929) ^ 207482976 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 622448929) ^ 16822944 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 622448929) ^ 31968 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_642150427 : Nat.Prime 642150427 := by
  apply lucas_primality 642150427 (5 : ZMod 642150427)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2039, 1), (52489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2039, 1), (52489, 1)] : List FactorBlock).map factorBlockValue).prod) = 642150427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_2039
      · exact prime_thirtyOneAC_52489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 642150427) ^ 321075213 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 642150427) ^ 214050142 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 642150427) ^ 314934 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 642150427) ^ 12234 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_736742561 : Nat.Prime 736742561 := by
  apply lucas_primality 736742561 (3 : ZMod 736742561)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (4604641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (4604641, 1)] : List FactorBlock).map factorBlockValue).prod) = 736742561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_4604641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 736742561) ^ 368371280 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 736742561) ^ 147348512 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 736742561) ^ 160 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_759289507 : Nat.Prime 759289507 := by
  apply lucas_primality 759289507 (2 : ZMod 759289507)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (331, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (331, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) = 759289507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_331
      · exact prime_thirtyOneAC_10333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 759289507) ^ 379644753 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 759289507) ^ 253096502 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 759289507) ^ 20521338 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 759289507) ^ 2293926 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 759289507) ^ 73482 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_802859927 : Nat.Prime 802859927 := by
  apply lucas_primality 802859927 (5 : ZMod 802859927)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (3317603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (3317603, 1)] : List FactorBlock).map factorBlockValue).prod) = 802859927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_3317603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 802859927) ^ 401429963 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 802859927) ^ 72987266 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 802859927) ^ 242 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_808078279 : Nat.Prime 808078279 := by
  apply lucas_primality 808078279 (3 : ZMod 808078279)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (59, 1), (326101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (59, 1), (326101, 1)] : List FactorBlock).map factorBlockValue).prod) = 808078279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_326101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 808078279) ^ 404039139 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 808078279) ^ 269359426 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 808078279) ^ 115439754 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 808078279) ^ 13696242 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 808078279) ^ 2478 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_872429057 : Nat.Prime 872429057 := by
  apply lucas_primality 872429057 (3 : ZMod 872429057)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (1703963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (1703963, 1)] : List FactorBlock).map factorBlockValue).prod) = 872429057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_1703963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 872429057) ^ 436214528 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 872429057) ^ 512 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_912832351 : Nat.Prime 912832351 := by
  apply lucas_primality 912832351 (3 : ZMod 912832351)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (103, 1), (59083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (103, 1), (59083, 1)] : List FactorBlock).map factorBlockValue).prod) = 912832351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_103
      · exact prime_thirtyOneAC_59083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 912832351) ^ 456416175 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 912832351) ^ 304277450 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 912832351) ^ 182566470 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 912832351) ^ 8862450 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 912832351) ^ 15450 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_919599391 : Nat.Prime 919599391 := by
  apply lucas_primality 919599391 (3 : ZMod 919599391)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (10217771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (10217771, 1)] : List FactorBlock).map factorBlockValue).prod) = 919599391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_10217771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 919599391) ^ 459799695 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 919599391) ^ 306533130 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 919599391) ^ 183919878 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 919599391) ^ 90 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_952534507 : Nat.Prime 952534507 := by
  apply lucas_primality 952534507 (2 : ZMod 952534507)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (187433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (187433, 1)] : List FactorBlock).map factorBlockValue).prod) = 952534507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_187433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 952534507) ^ 476267253 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 952534507) ^ 317511502 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 952534507) ^ 136076358 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 952534507) ^ 86594046 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 952534507) ^ 5082 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1108441039 : Nat.Prime 1108441039 := by
  apply lucas_primality 1108441039 (6 : ZMod 1108441039)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (157, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (157, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1108441039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_157
      · exact prime_thirtyOneAC_3643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1108441039) ^ 554220519 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1108441039) ^ 369480346 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1108441039) ^ 65202414 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1108441039) ^ 58339002 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1108441039) ^ 7060134 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1108441039) ^ 304266 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1181738057 : Nat.Prime 1181738057 := by
  apply lucas_primality 1181738057 (3 : ZMod 1181738057)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3863, 1), (38239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3863, 1), (38239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1181738057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3863
      · exact prime_thirtyOneAC_38239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1181738057) ^ 590869028 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1181738057) ^ 305912 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1181738057) ^ 30904 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1212306731 : Nat.Prime 1212306731 := by
  apply lucas_primality 1212306731 (2 : ZMod 1212306731)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (121230673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (121230673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1212306731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_121230673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1212306731) ^ 606153365 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1212306731) ^ 242461346 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1212306731) ^ 10 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_113
      · exact prime_thirtyOneAC_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1317134227 : Nat.Prime 1317134227 := by
  apply lucas_primality 1317134227 (2 : ZMod 1317134227)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (11553809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (11553809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1317134227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_11553809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1317134227) ^ 658567113 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317134227) ^ 439044742 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317134227) ^ 69322854 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317134227) ^ 114 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1347408371 : Nat.Prime 1347408371 := by
  apply lucas_primality 1347408371 (6 : ZMod 1347408371)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (11, 1), (19, 1), (59, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (11, 1), (19, 1), (59, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347408371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1347408371) ^ 673704185 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1347408371) ^ 269481674 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1347408371) ^ 192486910 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1347408371) ^ 122491670 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1347408371) ^ 70916230 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1347408371) ^ 22837430 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1347408371) ^ 6042190 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1486232981 : Nat.Prime 1486232981 := by
  apply lucas_primality 1486232981 (2 : ZMod 1486232981)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (74311649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (74311649, 1)] : List FactorBlock).map factorBlockValue).prod) = 1486232981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_74311649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1486232981) ^ 743116490 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1486232981) ^ 297246596 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1486232981) ^ 20 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1526575517 : Nat.Prime 1526575517 := by
  apply lucas_primality 1526575517 (2 : ZMod 1526575517)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (381643879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (381643879, 1)] : List FactorBlock).map factorBlockValue).prod) = 1526575517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_381643879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1526575517) ^ 763287758 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526575517) ^ 4 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1672486201 : Nat.Prime 1672486201 := by
  apply lucas_primality 1672486201 (19 : ZMod 1672486201)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (7, 1), (11, 2), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (7, 1), (11, 2), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1672486201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1672486201) ^ 836243100 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 1672486201) ^ 557495400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 1672486201) ^ 334497240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 1672486201) ^ 238926600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 1672486201) ^ 152044200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (19 : ZMod 1672486201) ^ 1524600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1954588523 : Nat.Prime 1954588523 := by
  apply lucas_primality 1954588523 (2 : ZMod 1954588523)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16979, 1), (57559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16979, 1), (57559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1954588523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_16979
      · exact prime_thirtyOneAC_57559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1954588523) ^ 977294261 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954588523) ^ 115118 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954588523) ^ 33958 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2230445479 : Nat.Prime 2230445479 := by
  apply lucas_primality 2230445479 (3 : ZMod 2230445479)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (371740913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (371740913, 1)] : List FactorBlock).map factorBlockValue).prod) = 2230445479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_371740913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2230445479) ^ 1115222739 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2230445479) ^ 743481826 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2230445479) ^ 6 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2354202161 : Nat.Prime 2354202161 := by
  apply lucas_primality 2354202161 (3 : ZMod 2354202161)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (499, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (499, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 2354202161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_499
      · exact prime_thirtyOneAC_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2354202161) ^ 1177101080 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2354202161) ^ 470840432 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2354202161) ^ 138482480 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2354202161) ^ 4717840 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2354202161) ^ 678640 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2674532153 : Nat.Prime 2674532153 := by
  apply lucas_primality 2674532153 (3 : ZMod 2674532153)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (569, 1), (587551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (569, 1), (587551, 1)] : List FactorBlock).map factorBlockValue).prod) = 2674532153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_569
      · exact prime_thirtyOneAC_587551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2674532153) ^ 1337266076 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2674532153) ^ 4700408 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2674532153) ^ 4552 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2694816743 : Nat.Prime 2694816743 := by
  apply lucas_primality 2694816743 (5 : ZMod 2694816743)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1347408371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1347408371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2694816743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_1347408371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2694816743) ^ 1347408371 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 2694816743) ^ 2 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2723287183 : Nat.Prime 2723287183 := by
  apply lucas_primality 2723287183 (3 : ZMod 2723287183)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (5894561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (5894561, 1)] : List FactorBlock).map factorBlockValue).prod) = 2723287183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_5894561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2723287183) ^ 1361643591 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723287183) ^ 907762394 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723287183) ^ 389041026 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723287183) ^ 247571562 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2723287183) ^ 462 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2817303341 : Nat.Prime 2817303341 := by
  apply lucas_primality 2817303341 (3 : ZMod 2817303341)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (263, 1), (535609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (263, 1), (535609, 1)] : List FactorBlock).map factorBlockValue).prod) = 2817303341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_263
      · exact prime_thirtyOneAC_535609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2817303341) ^ 1408651670 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2817303341) ^ 563460668 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2817303341) ^ 10712180 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 2817303341) ^ 5260 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3203064349 : Nat.Prime 3203064349 := by
  apply lucas_primality 3203064349 (2 : ZMod 3203064349)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (24265639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (24265639, 1)] : List FactorBlock).map factorBlockValue).prod) = 3203064349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_24265639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3203064349) ^ 1601532174 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3203064349) ^ 1067688116 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3203064349) ^ 291187668 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3203064349) ^ 132 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3276316997 : Nat.Prime 3276316997 := by
  apply lucas_primality 3276316997 (2 : ZMod 3276316997)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (22137277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (22137277, 1)] : List FactorBlock).map factorBlockValue).prod) = 3276316997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_22137277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3276316997) ^ 1638158498 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3276316997) ^ 88549108 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3276316997) ^ 148 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3295842833 : Nat.Prime 3295842833 := by
  apply lucas_primality 3295842833 (3 : ZMod 3295842833)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (205990177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (205990177, 1)] : List FactorBlock).map factorBlockValue).prod) = 3295842833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_205990177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3295842833) ^ 1647921416 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3295842833) ^ 16 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3388799731 : Nat.Prime 3388799731 := by
  apply lucas_primality 3388799731 (10 : ZMod 3388799731)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4723, 1), (23917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4723, 1), (23917, 1)] : List FactorBlock).map factorBlockValue).prod) = 3388799731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_4723
      · exact prime_thirtyOneAC_23917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3388799731) ^ 1694399865 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3388799731) ^ 1129599910 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3388799731) ^ 677759946 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3388799731) ^ 717510 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3388799731) ^ 141690 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3440996113 : Nat.Prime 3440996113 := by
  apply lucas_primality 3440996113 (5 : ZMod 3440996113)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (59, 1), (71473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (59, 1), (71473, 1)] : List FactorBlock).map factorBlockValue).prod) = 3440996113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_71473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3440996113) ^ 1720498056 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 3440996113) ^ 1146998704 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 3440996113) ^ 202411536 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 3440996113) ^ 58321968 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 3440996113) ^ 48144 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3475051057 : Nat.Prime 3475051057 := by
  apply lucas_primality 3475051057 (10 : ZMod 3475051057)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (19, 1), (74713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (19, 1), (74713, 1)] : List FactorBlock).map factorBlockValue).prod) = 3475051057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_74713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3475051057) ^ 1737525528 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3475051057) ^ 1158350352 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3475051057) ^ 204414768 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3475051057) ^ 182897424 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3475051057) ^ 46512 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3851434333 : Nat.Prime 3851434333 := by
  apply lucas_primality 3851434333 (2 : ZMod 3851434333)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (59, 1), (239, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (59, 1), (239, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 3851434333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_239
      · exact prime_thirtyOneAC_281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3851434333) ^ 1925717166 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3851434333) ^ 1283811444 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3851434333) ^ 65278548 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3851434333) ^ 16114788 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3851434333) ^ 13706172 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4041787301 : Nat.Prime 4041787301 := by
  apply lucas_primality 4041787301 (3 : ZMod 4041787301)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (40417873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (40417873, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041787301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_40417873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4041787301) ^ 2020893650 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041787301) ^ 808357460 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4041787301) ^ 100 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4331009479 : Nat.Prime 4331009479 := by
  apply lucas_primality 4331009479 (3 : ZMod 4331009479)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10987, 1), (65699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10987, 1), (65699, 1)] : List FactorBlock).map factorBlockValue).prod) = 4331009479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_10987
      · exact prime_thirtyOneAC_65699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4331009479) ^ 2165504739 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4331009479) ^ 1443669826 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4331009479) ^ 394194 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4331009479) ^ 65922 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4433764157 : Nat.Prime 4433764157 := by
  apply lucas_primality 4433764157 (2 : ZMod 4433764157)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1108441039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1108441039, 1)] : List FactorBlock).map factorBlockValue).prod) = 4433764157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_1108441039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4433764157) ^ 2216882078 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 4433764157) ^ 4 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_5971457539 : Nat.Prime 5971457539 := by
  apply lucas_primality 5971457539 (2 : ZMod 5971457539)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1409, 1), (26161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1409, 1), (26161, 1)] : List FactorBlock).map factorBlockValue).prod) = 5971457539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_1409
      · exact prime_thirtyOneAC_26161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5971457539) ^ 2985728769 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5971457539) ^ 1990485846 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5971457539) ^ 4238082 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5971457539) ^ 228258 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_7084069841 : Nat.Prime 7084069841 := by
  apply lucas_primality 7084069841 (3 : ZMod 7084069841)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (88550873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (88550873, 1)] : List FactorBlock).map factorBlockValue).prod) = 7084069841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_88550873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7084069841) ^ 3542034920 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 7084069841) ^ 1416813968 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 7084069841) ^ 80 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_7934984999 : Nat.Prime 7934984999 := by
  apply lucas_primality 7934984999 (7 : ZMod 7934984999)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (37, 1), (3459017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (37, 1), (3459017, 1)] : List FactorBlock).map factorBlockValue).prod) = 7934984999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_3459017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7934984999) ^ 3967492499 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 7934984999) ^ 255967258 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 7934984999) ^ 214459054 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 7934984999) ^ 2294 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_8783084521 : Nat.Prime 8783084521 := by
  apply lucas_primality 8783084521 (17 : ZMod 8783084521)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (23, 1), (151537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (23, 1), (151537, 1)] : List FactorBlock).map factorBlockValue).prod) = 8783084521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_151537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 8783084521) ^ 4391542260 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (17 : ZMod 8783084521) ^ 2927694840 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (17 : ZMod 8783084521) ^ 1756616904 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (17 : ZMod 8783084521) ^ 1254726360 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (17 : ZMod 8783084521) ^ 381873240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (17 : ZMod 8783084521) ^ 57960 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_9185532353 : Nat.Prime 9185532353 := by
  apply lucas_primality 9185532353 (3 : ZMod 9185532353)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (8461, 1), (16963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (8461, 1), (16963, 1)] : List FactorBlock).map factorBlockValue).prod) = 9185532353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_8461
      · exact prime_thirtyOneAC_16963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9185532353) ^ 4592766176 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 9185532353) ^ 1085632 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 9185532353) ^ 541504 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_10007392883 : Nat.Prime 10007392883 := by
  apply lucas_primality 10007392883 (2 : ZMod 10007392883)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1051, 1), (4760891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1051, 1), (4760891, 1)] : List FactorBlock).map factorBlockValue).prod) = 10007392883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_1051
      · exact prime_thirtyOneAC_4760891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10007392883) ^ 5003696441 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 10007392883) ^ 9521782 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 10007392883) ^ 2102 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_10202690741 : Nat.Prime 10202690741 := by
  apply lucas_primality 10202690741 (3 : ZMod 10202690741)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (101, 1), (459167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (101, 1), (459167, 1)] : List FactorBlock).map factorBlockValue).prod) = 10202690741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_101
      · exact prime_thirtyOneAC_459167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10202690741) ^ 5101345370 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 10202690741) ^ 2040538148 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 10202690741) ^ 927517340 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 10202690741) ^ 101016740 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 10202690741) ^ 22220 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_12417592507 : Nat.Prime 12417592507 := by
  apply lucas_primality 12417592507 (3 : ZMod 12417592507)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (239, 1), (46307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (239, 1), (46307, 1)] : List FactorBlock).map factorBlockValue).prod) = 12417592507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_239
      · exact prime_thirtyOneAC_46307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12417592507) ^ 6208796253 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 12417592507) ^ 4139197502 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 12417592507) ^ 1128872046 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 12417592507) ^ 730446618 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 12417592507) ^ 51956454 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 12417592507) ^ 268158 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_13052550013 : Nat.Prime 13052550013 := by
  apply lucas_primality 13052550013 (2 : ZMod 13052550013)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4297, 1), (253133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4297, 1), (253133, 1)] : List FactorBlock).map factorBlockValue).prod) = 13052550013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_4297
      · exact prime_thirtyOneAC_253133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13052550013) ^ 6526275006 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 13052550013) ^ 4350850004 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 13052550013) ^ 3037596 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 13052550013) ^ 51564 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_13261836377 : Nat.Prime 13261836377 := by
  apply lucas_primality 13261836377 (3 : ZMod 13261836377)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10987, 1), (150881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10987, 1), (150881, 1)] : List FactorBlock).map factorBlockValue).prod) = 13261836377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_10987
      · exact prime_thirtyOneAC_150881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 13261836377) ^ 6630918188 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 13261836377) ^ 1207048 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 13261836377) ^ 87896 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_14168139683 : Nat.Prime 14168139683 := by
  apply lucas_primality 14168139683 (2 : ZMod 14168139683)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7084069841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7084069841, 1)] : List FactorBlock).map factorBlockValue).prod) = 14168139683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7084069841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14168139683) ^ 7084069841 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 14168139683) ^ 2 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_16659257077 : Nat.Prime 16659257077 := by
  apply lucas_primality 16659257077 (5 : ZMod 16659257077)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (19, 1), (67, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (19, 1), (67, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) = 16659257077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_67
      · exact prime_thirtyOneAC_4721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16659257077) ^ 8329628538 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 16659257077) ^ 5553085692 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 16659257077) ^ 2379893868 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 16659257077) ^ 1514477916 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 16659257077) ^ 876803004 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 16659257077) ^ 248645628 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 16659257077) ^ 3528756 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_18577071983 : Nat.Prime 18577071983 := by
  apply lucas_primality 18577071983 (5 : ZMod 18577071983)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (97, 1), (1954247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (97, 1), (1954247, 1)] : List FactorBlock).map factorBlockValue).prod) = 18577071983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_97
      · exact prime_thirtyOneAC_1954247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18577071983) ^ 9288535991 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 18577071983) ^ 2653867426 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 18577071983) ^ 191516206 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 18577071983) ^ 9506 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_22570030039 : Nat.Prime 22570030039 := by
  apply lucas_primality 22570030039 (7 : ZMod 22570030039)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (63757147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (63757147, 1)] : List FactorBlock).map factorBlockValue).prod) = 22570030039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_63757147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 22570030039) ^ 11285015019 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 22570030039) ^ 7523343346 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 22570030039) ^ 382542882 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 22570030039) ^ 354 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_24483717077 : Nat.Prime 24483717077 := by
  apply lucas_primality 24483717077 (2 : ZMod 24483717077)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (67262959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (67262959, 1)] : List FactorBlock).map factorBlockValue).prod) = 24483717077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_67262959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24483717077) ^ 12241858538 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 24483717077) ^ 3497673868 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 24483717077) ^ 1883362852 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 24483717077) ^ 364 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_35470113257 : Nat.Prime 35470113257 := by
  apply lucas_primality 35470113257 (3 : ZMod 35470113257)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4433764157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4433764157, 1)] : List FactorBlock).map factorBlockValue).prod) = 35470113257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_4433764157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 35470113257) ^ 17735056628 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 35470113257) ^ 8 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_40020569471 : Nat.Prime 40020569471 := by
  apply lucas_primality 40020569471 (14 : ZMod 40020569471)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (3469, 1), (164809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (3469, 1), (164809, 1)] : List FactorBlock).map factorBlockValue).prod) = 40020569471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_3469
      · exact prime_thirtyOneAC_164809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 40020569471) ^ 20010284735 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (14 : ZMod 40020569471) ^ 8004113894 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (14 : ZMod 40020569471) ^ 5717224210 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (14 : ZMod 40020569471) ^ 11536630 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (14 : ZMod 40020569471) ^ 242830 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_48856027193 : Nat.Prime 48856027193 := by
  apply lucas_primality 48856027193 (3 : ZMod 48856027193)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (872429057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (872429057, 1)] : List FactorBlock).map factorBlockValue).prod) = 48856027193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_872429057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48856027193) ^ 24428013596 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 48856027193) ^ 6979432456 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 48856027193) ^ 56 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_51483551611 : Nat.Prime 51483551611 := by
  apply lucas_primality 51483551611 (3 : ZMod 51483551611)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9241, 1), (185707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9241, 1), (185707, 1)] : List FactorBlock).map factorBlockValue).prod) = 51483551611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_9241
      · exact prime_thirtyOneAC_185707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51483551611) ^ 25741775805 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 51483551611) ^ 17161183870 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 51483551611) ^ 10296710322 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 51483551611) ^ 5571210 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 51483551611) ^ 277230 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_55066036951 : Nat.Prime 55066036951 := by
  apply lucas_primality 55066036951 (6 : ZMod 55066036951)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (40789657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (40789657, 1)] : List FactorBlock).map factorBlockValue).prod) = 55066036951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_40789657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 55066036951) ^ 27533018475 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 55066036951) ^ 18355345650 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 55066036951) ^ 11013207390 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 55066036951) ^ 1350 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_60159925027 : Nat.Prime 60159925027 := by
  apply lucas_primality 60159925027 (2 : ZMod 60159925027)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (103, 1), (337, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (103, 1), (337, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 60159925027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_73
      · exact prime_thirtyOneAC_103
      · exact prime_thirtyOneAC_337
      · exact prime_thirtyOneAC_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60159925027) ^ 30079962513 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 60159925027) ^ 20053308342 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 60159925027) ^ 824108562 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 60159925027) ^ 584076942 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 60159925027) ^ 178516098 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 60159925027) ^ 45610254 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_63479879993 : Nat.Prime 63479879993 := by
  apply lucas_primality 63479879993 (3 : ZMod 63479879993)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7934984999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7934984999, 1)] : List FactorBlock).map factorBlockValue).prod) = 63479879993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7934984999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 63479879993) ^ 31739939996 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 63479879993) ^ 8 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_68846054699 : Nat.Prime 68846054699 := by
  apply lucas_primality 68846054699 (2 : ZMod 68846054699)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (9349, 1), (160087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (9349, 1), (160087, 1)] : List FactorBlock).map factorBlockValue).prod) = 68846054699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_9349
      · exact prime_thirtyOneAC_160087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68846054699) ^ 34423027349 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 68846054699) ^ 2993306726 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 68846054699) ^ 7364002 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 68846054699) ^ 430054 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_69319112791 : Nat.Prime 69319112791 := by
  apply lucas_primality 69319112791 (3 : ZMod 69319112791)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (419, 1), (324391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (419, 1), (324391, 1)] : List FactorBlock).map factorBlockValue).prod) = 69319112791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_419
      · exact prime_thirtyOneAC_324391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69319112791) ^ 34659556395 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 69319112791) ^ 23106370930 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 69319112791) ^ 13863822558 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 69319112791) ^ 4077594870 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 69319112791) ^ 165439410 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 69319112791) ^ 213690 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_70467415679 : Nat.Prime 70467415679 := by
  apply lucas_primality 70467415679 (11 : ZMod 70467415679)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3203064349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3203064349, 1)] : List FactorBlock).map factorBlockValue).prod) = 70467415679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_3203064349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 70467415679) ^ 35233707839 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 70467415679) ^ 6406128698 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 70467415679) ^ 22 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_72885757927 : Nat.Prime 72885757927 := by
  apply lucas_primality 72885757927 (3 : ZMod 72885757927)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (829, 1), (14653349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (829, 1), (14653349, 1)] : List FactorBlock).map factorBlockValue).prod) = 72885757927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_829
      · exact prime_thirtyOneAC_14653349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 72885757927) ^ 36442878963 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 72885757927) ^ 24295252642 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 72885757927) ^ 87920094 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 72885757927) ^ 4974 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_91229867669 : Nat.Prime 91229867669 := by
  apply lucas_primality 91229867669 (2 : ZMod 91229867669)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (8081, 1), (166021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (8081, 1), (166021, 1)] : List FactorBlock).map factorBlockValue).prod) = 91229867669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_8081
      · exact prime_thirtyOneAC_166021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91229867669) ^ 45614933834 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 91229867669) ^ 5366462804 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 91229867669) ^ 11289428 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 91229867669) ^ 549508 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_111634546297 : Nat.Prime 111634546297 := by
  apply lucas_primality 111634546297 (5 : ZMod 111634546297)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (1439, 1), (35521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (1439, 1), (35521, 1)] : List FactorBlock).map factorBlockValue).prod) = 111634546297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_1439
      · exact prime_thirtyOneAC_35521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 111634546297) ^ 55817273148 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 111634546297) ^ 37211515432 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 111634546297) ^ 15947792328 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 111634546297) ^ 8587272792 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 111634546297) ^ 77577864 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 111634546297) ^ 3142776 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_121253619031 : Nat.Prime 121253619031 := by
  apply lucas_primality 121253619031 (29 : ZMod 121253619031)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4041787301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4041787301, 1)] : List FactorBlock).map factorBlockValue).prod) = 121253619031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_4041787301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 121253619031) ^ 60626809515 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (29 : ZMod 121253619031) ^ 40417873010 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (29 : ZMod 121253619031) ^ 24250723806 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (29 : ZMod 121253619031) ^ 30 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_126173256427 : Nat.Prime 126173256427 := by
  apply lucas_primality 126173256427 (23 : ZMod 126173256427)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (31, 1), (233, 1), (138637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (31, 1), (233, 1), (138637, 1)] : List FactorBlock).map factorBlockValue).prod) = 126173256427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_233
      · exact prime_thirtyOneAC_138637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 126173256427) ^ 63086628213 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 126173256427) ^ 42057752142 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 126173256427) ^ 18024750918 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 126173256427) ^ 4070105046 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 126173256427) ^ 541516122 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 126173256427) ^ 910098 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_133760968291 : Nat.Prime 133760968291 := by
  apply lucas_primality 133760968291 (2 : ZMod 133760968291)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1486232981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1486232981, 1)] : List FactorBlock).map factorBlockValue).prod) = 133760968291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_1486232981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 133760968291) ^ 66880484145 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 133760968291) ^ 44586989430 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 133760968291) ^ 26752193658 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 133760968291) ^ 90 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_140629792081 : Nat.Prime 140629792081 := by
  apply lucas_primality 140629792081 (31 : ZMod 140629792081)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (857, 1), (683731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (857, 1), (683731, 1)] : List FactorBlock).map factorBlockValue).prod) = 140629792081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_857
      · exact prime_thirtyOneAC_683731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 140629792081) ^ 70314896040 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 140629792081) ^ 46876597360 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 140629792081) ^ 28125958416 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 140629792081) ^ 164095440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 140629792081) ^ 205680 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_147319016681 : Nat.Prime 147319016681 := by
  apply lucas_primality 147319016681 (3 : ZMod 147319016681)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (107, 1), (3129121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (107, 1), (3129121, 1)] : List FactorBlock).map factorBlockValue).prod) = 147319016681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_107
      · exact prime_thirtyOneAC_3129121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 147319016681) ^ 73659508340 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 147319016681) ^ 29463803336 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 147319016681) ^ 13392637880 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 147319016681) ^ 1376813240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 147319016681) ^ 47080 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_220452776473 : Nat.Prime 220452776473 := by
  apply lucas_primality 220452776473 (7 : ZMod 220452776473)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (9185532353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (9185532353, 1)] : List FactorBlock).map factorBlockValue).prod) = 220452776473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_9185532353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 220452776473) ^ 110226388236 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 220452776473) ^ 73484258824 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 220452776473) ^ 24 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_265989678377 : Nat.Prime 265989678377 := by
  apply lucas_primality 265989678377 (3 : ZMod 265989678377)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2383, 1), (13952459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2383, 1), (13952459, 1)] : List FactorBlock).map factorBlockValue).prod) = 265989678377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_2383
      · exact prime_thirtyOneAC_13952459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 265989678377) ^ 132994839188 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 265989678377) ^ 111619672 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 265989678377) ^ 19064 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_362034827303 : Nat.Prime 362034827303 := by
  apply lucas_primality 362034827303 (5 : ZMod 362034827303)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (3851434333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (3851434333, 1)] : List FactorBlock).map factorBlockValue).prod) = 362034827303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_3851434333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362034827303) ^ 181017413651 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 362034827303) ^ 7702868666 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 362034827303) ^ 94 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_378286419449 : Nat.Prime 378286419449 := by
  apply lucas_primality 378286419449 (3 : ZMod 378286419449)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (127, 1), (139, 1), (382661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (127, 1), (139, 1), (382661, 1)] : List FactorBlock).map factorBlockValue).prod) = 378286419449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_127
      · exact prime_thirtyOneAC_139
      · exact prime_thirtyOneAC_382661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 378286419449) ^ 189143209724 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 378286419449) ^ 54040917064 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 378286419449) ^ 2978633224 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 378286419449) ^ 2721485032 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 378286419449) ^ 988568 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_446241887453 : Nat.Prime 446241887453 := by
  apply lucas_primality 446241887453 (2 : ZMod 446241887453)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (239, 1), (466780217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (239, 1), (466780217, 1)] : List FactorBlock).map factorBlockValue).prod) = 446241887453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_239
      · exact prime_thirtyOneAC_466780217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 446241887453) ^ 223120943726 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 446241887453) ^ 1867120868 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 446241887453) ^ 956 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_397
      · exact prime_thirtyOneAC_2531
      · exact prime_thirtyOneAC_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_497434820581 : Nat.Prime 497434820581 := by
  apply lucas_primality 497434820581 (2 : ZMod 497434820581)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (37, 1), (74689913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (37, 1), (74689913, 1)] : List FactorBlock).map factorBlockValue).prod) = 497434820581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_74689913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 497434820581) ^ 248717410290 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 497434820581) ^ 165811606860 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 497434820581) ^ 99486964116 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 497434820581) ^ 13444184340 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 497434820581) ^ 6660 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_586272326317 : Nat.Prime 586272326317 := by
  apply lucas_primality 586272326317 (2 : ZMod 586272326317)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (48856027193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (48856027193, 1)] : List FactorBlock).map factorBlockValue).prod) = 586272326317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_48856027193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 586272326317) ^ 293136163158 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 586272326317) ^ 195424108772 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 586272326317) ^ 12 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_613740796223 : Nat.Prime 613740796223 := by
  apply lucas_primality 613740796223 (5 : ZMod 613740796223)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (1954588523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (1954588523, 1)] : List FactorBlock).map factorBlockValue).prod) = 613740796223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_157
      · exact prime_thirtyOneAC_1954588523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 613740796223) ^ 306870398111 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 613740796223) ^ 3909177046 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 613740796223) ^ 314 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_623427952331 : Nat.Prime 623427952331 := by
  apply lucas_primality 623427952331 (2 : ZMod 623427952331)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (1741, 1), (2106389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (1741, 1), (2106389, 1)] : List FactorBlock).map factorBlockValue).prod) = 623427952331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_1741
      · exact prime_thirtyOneAC_2106389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 623427952331) ^ 311713976165 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 623427952331) ^ 124685590466 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 623427952331) ^ 36672232490 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 623427952331) ^ 358086130 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 623427952331) ^ 295970 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_684432719779 : Nat.Prime 684432719779 := by
  apply lucas_primality 684432719779 (2 : ZMod 684432719779)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (9949, 1), (90281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (9949, 1), (90281, 1)] : List FactorBlock).map factorBlockValue).prod) = 684432719779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_127
      · exact prime_thirtyOneAC_9949
      · exact prime_thirtyOneAC_90281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 684432719779) ^ 342216359889 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 684432719779) ^ 228144239926 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 684432719779) ^ 5389234014 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 684432719779) ^ 68794122 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 684432719779) ^ 7581138 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_729838941353 : Nat.Prime 729838941353 := by
  apply lucas_primality 729838941353 (3 : ZMod 729838941353)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (91229867669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (91229867669, 1)] : List FactorBlock).map factorBlockValue).prod) = 729838941353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_91229867669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 729838941353) ^ 364919470676 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 729838941353) ^ 8 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_784204162211 : Nat.Prime 784204162211 := by
  apply lucas_primality 784204162211 (2 : ZMod 784204162211)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (73, 1), (727, 1), (211093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (73, 1), (727, 1), (211093, 1)] : List FactorBlock).map factorBlockValue).prod) = 784204162211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_73
      · exact prime_thirtyOneAC_727
      · exact prime_thirtyOneAC_211093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 784204162211) ^ 392102081105 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 784204162211) ^ 156840832442 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 784204162211) ^ 112029166030 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 784204162211) ^ 10742522770 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 784204162211) ^ 1078685230 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 784204162211) ^ 3714970 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1422859692403 : Nat.Prime 1422859692403 := by
  apply lucas_primality 1422859692403 (2 : ZMod 1422859692403)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (8783084521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (8783084521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1422859692403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_8783084521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1422859692403) ^ 711429846201 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1422859692403) ^ 474286564134 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1422859692403) ^ 162 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_35279
      · exact prime_thirtyOneAC_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1544506548331 : Nat.Prime 1544506548331 := by
  apply lucas_primality 1544506548331 (3 : ZMod 1544506548331)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (51483551611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (51483551611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1544506548331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_51483551611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1544506548331) ^ 772253274165 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1544506548331) ^ 514835516110 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1544506548331) ^ 308901309666 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1544506548331) ^ 30 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1702565436337 : Nat.Prime 1702565436337 := by
  apply lucas_primality 1702565436337 (5 : ZMod 1702565436337)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (35470113257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (35470113257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1702565436337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_35470113257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1702565436337) ^ 851282718168 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 1702565436337) ^ 567521812112 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 1702565436337) ^ 48 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1934752242637 : Nat.Prime 1934752242637 := by
  apply lucas_primality 1934752242637 (2 : ZMod 1934752242637)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5971457539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5971457539, 1)] : List FactorBlock).map factorBlockValue).prod) = 1934752242637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5971457539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1934752242637) ^ 967376121318 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1934752242637) ^ 644917414212 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1934752242637) ^ 324 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1989275456551 : Nat.Prime 1989275456551 := by
  apply lucas_primality 1989275456551 (6 : ZMod 1989275456551)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13261836377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13261836377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1989275456551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_13261836377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1989275456551) ^ 994637728275 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1989275456551) ^ 663091818850 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1989275456551) ^ 397855091310 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 1989275456551) ^ 150 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2846496204389 : Nat.Prime 2846496204389 := by
  apply lucas_primality 2846496204389 (2 : ZMod 2846496204389)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (587, 1), (1212306731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (587, 1), (1212306731, 1)] : List FactorBlock).map factorBlockValue).prod) = 2846496204389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_587
      · exact prime_thirtyOneAC_1212306731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2846496204389) ^ 1423248102194 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2846496204389) ^ 4849226924 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2846496204389) ^ 2348 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3138255539893 : Nat.Prime 3138255539893 := by
  apply lucas_primality 3138255539893 (2 : ZMod 3138255539893)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (71, 1), (457, 1), (467, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (71, 1), (457, 1), (467, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 3138255539893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_71
      · exact prime_thirtyOneAC_457
      · exact prime_thirtyOneAC_467
      · exact prime_thirtyOneAC_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3138255539893) ^ 1569127769946 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138255539893) ^ 1046085179964 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138255539893) ^ 285295958172 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138255539893) ^ 44200782252 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138255539893) ^ 6867079956 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138255539893) ^ 6720033276 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138255539893) ^ 6000488604 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3222316518409 : Nat.Prime 3222316518409 := by
  apply lucas_primality 3222316518409 (11 : ZMod 3222316518409)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (19, 1), (181191887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (19, 1), (181191887, 1)] : List FactorBlock).map factorBlockValue).prod) = 3222316518409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_181191887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3222316518409) ^ 1611158259204 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 3222316518409) ^ 1074105506136 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 3222316518409) ^ 247870501416 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 3222316518409) ^ 169595606232 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 3222316518409) ^ 17784 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3304905766951 : Nat.Prime 3304905766951 := by
  apply lucas_primality 3304905766951 (6 : ZMod 3304905766951)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31, 1), (43, 1), (16528661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31, 1), (43, 1), (16528661, 1)] : List FactorBlock).map factorBlockValue).prod) = 3304905766951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_16528661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3304905766951) ^ 1652452883475 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 3304905766951) ^ 1101635255650 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 3304905766951) ^ 660981153390 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 3304905766951) ^ 106609863450 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 3304905766951) ^ 76858273650 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 3304905766951) ^ 199950 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3438062887697 : Nat.Prime 3438062887697 := by
  apply lucas_primality 3438062887697 (3 : ZMod 3438062887697)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (283, 1), (759289507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (283, 1), (759289507, 1)] : List FactorBlock).map factorBlockValue).prod) = 3438062887697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_283
      · exact prime_thirtyOneAC_759289507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3438062887697) ^ 1719031443848 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3438062887697) ^ 12148632112 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3438062887697) ^ 4528 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3441430984913 : Nat.Prime 3441430984913 := by
  apply lucas_primality 3441430984913 (3 : ZMod 3441430984913)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (61, 1), (233, 1), (2843, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (61, 1), (233, 1), (2843, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) = 3441430984913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_61
      · exact prime_thirtyOneAC_233
      · exact prime_thirtyOneAC_2843
      · exact prime_thirtyOneAC_5323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3441430984913) ^ 1720715492456 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3441430984913) ^ 56416901392 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3441430984913) ^ 14770090064 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3441430984913) ^ 1210492784 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3441430984913) ^ 646520944 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3761952324973 : Nat.Prime 3761952324973 := by
  apply lucas_primality 3761952324973 (2 : ZMod 3761952324973)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (23, 2), (31190531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (23, 2), (31190531, 1)] : List FactorBlock).map factorBlockValue).prod) = 3761952324973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_31190531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3761952324973) ^ 1880976162486 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3761952324973) ^ 1253984108324 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3761952324973) ^ 197997490788 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3761952324973) ^ 163563144564 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3761952324973) ^ 120612 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_5227955622437 : Nat.Prime 5227955622437 := by
  apply lucas_primality 5227955622437 (2 : ZMod 5227955622437)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (577, 1), (6659, 1), (10973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (577, 1), (6659, 1), (10973, 1)] : List FactorBlock).map factorBlockValue).prod) = 5227955622437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_577
      · exact prime_thirtyOneAC_6659
      · exact prime_thirtyOneAC_10973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5227955622437) ^ 2613977811218 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5227955622437) ^ 168643729756 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5227955622437) ^ 9060581668 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5227955622437) ^ 785096204 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5227955622437) ^ 476438132 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_5581079251037 : Nat.Prime 5581079251037 := by
  apply lucas_primality 5581079251037 (2 : ZMod 5581079251037)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (2549, 1), (2837, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (2549, 1), (2837, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) = 5581079251037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_61
      · exact prime_thirtyOneAC_2549
      · exact prime_thirtyOneAC_2837
      · exact prime_thirtyOneAC_3163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5581079251037) ^ 2790539625518 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5581079251037) ^ 91493102476 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5581079251037) ^ 2189517164 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5581079251037) ^ 1967246828 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 5581079251037) ^ 1764489172 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_5651488570649 : Nat.Prime 5651488570649 := by
  apply lucas_primality 5651488570649 (3 : ZMod 5651488570649)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (269, 1), (114180713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (269, 1), (114180713, 1)] : List FactorBlock).map factorBlockValue).prod) = 5651488570649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_269
      · exact prime_thirtyOneAC_114180713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5651488570649) ^ 2825744285324 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 5651488570649) ^ 245716894376 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 5651488570649) ^ 21009251192 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 5651488570649) ^ 49496 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_5994254204329 : Nat.Prime 5994254204329 := by
  apply lucas_primality 5994254204329 (7 : ZMod 5994254204329)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (101, 1), (4073, 1), (46703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (101, 1), (4073, 1), (46703, 1)] : List FactorBlock).map factorBlockValue).prod) = 5994254204329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_101
      · exact prime_thirtyOneAC_4073
      · exact prime_thirtyOneAC_46703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5994254204329) ^ 2997127102164 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 5994254204329) ^ 1998084734776 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 5994254204329) ^ 461096477256 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 5994254204329) ^ 59349051528 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 5994254204329) ^ 1471704936 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 5994254204329) ^ 128348376 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_6728051467091 : Nat.Prime 6728051467091 := by
  apply lucas_primality 6728051467091 (2 : ZMod 6728051467091)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (61, 1), (103, 1), (4655801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (61, 1), (103, 1), (4655801, 1)] : List FactorBlock).map factorBlockValue).prod) = 6728051467091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_61
      · exact prime_thirtyOneAC_103
      · exact prime_thirtyOneAC_4655801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6728051467091) ^ 3364025733545 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 6728051467091) ^ 1345610293418 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 6728051467091) ^ 292523976830 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 6728051467091) ^ 110295925690 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 6728051467091) ^ 65320888030 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 6728051467091) ^ 1445090 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_11165596354721 : Nat.Prime 11165596354721 := by
  apply lucas_primality 11165596354721 (3 : ZMod 11165596354721)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (151, 1), (462152167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (151, 1), (462152167, 1)] : List FactorBlock).map factorBlockValue).prod) = 11165596354721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_151
      · exact prime_thirtyOneAC_462152167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11165596354721) ^ 5582798177360 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 11165596354721) ^ 2233119270944 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 11165596354721) ^ 73944346720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 11165596354721) ^ 24160 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_11439350643067 : Nat.Prime 11439350643067 := by
  apply lucas_primality 11439350643067 (3 : ZMod 11439350643067)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (521, 1), (25667, 1), (142573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (521, 1), (25667, 1), (142573, 1)] : List FactorBlock).map factorBlockValue).prod) = 11439350643067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_521
      · exact prime_thirtyOneAC_25667
      · exact prime_thirtyOneAC_142573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11439350643067) ^ 5719675321533 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 11439350643067) ^ 3813116881022 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 11439350643067) ^ 21956527146 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 11439350643067) ^ 445683198 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 11439350643067) ^ 80235042 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_15277955997907 : Nat.Prime 15277955997907 := by
  apply lucas_primality 15277955997907 (2 : ZMod 15277955997907)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (121253619031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (121253619031, 1)] : List FactorBlock).map factorBlockValue).prod) = 15277955997907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_121253619031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15277955997907) ^ 7638977998953 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 15277955997907) ^ 5092651999302 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 15277955997907) ^ 2182565142558 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 15277955997907) ^ 126 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_16404651192493 : Nat.Prime 16404651192493 := by
  apply lucas_primality 16404651192493 (2 : ZMod 16404651192493)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (31, 1), (157, 1), (571, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (31, 1), (157, 1), (571, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) = 16404651192493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_157
      · exact prime_thirtyOneAC_571
      · exact prime_thirtyOneAC_6073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16404651192493) ^ 8202325596246 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 16404651192493) ^ 5468217064164 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 16404651192493) ^ 529182296532 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 16404651192493) ^ 104488224156 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 16404651192493) ^ 28729686852 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 16404651192493) ^ 2701243404 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_22261700055857 : Nat.Prime 22261700055857 := by
  apply lucas_primality 22261700055857 (3 : ZMod 22261700055857)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1733, 1), (802859927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1733, 1), (802859927, 1)] : List FactorBlock).map factorBlockValue).prod) = 22261700055857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_1733
      · exact prime_thirtyOneAC_802859927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22261700055857) ^ 11130850027928 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 22261700055857) ^ 12845758832 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 22261700055857) ^ 27728 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_24097061922463 : Nat.Prime 24097061922463 := by
  apply lucas_primality 24097061922463 (3 : ZMod 24097061922463)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (446241887453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (446241887453, 1)] : List FactorBlock).map factorBlockValue).prod) = 24097061922463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_446241887453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24097061922463) ^ 12048530961231 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 24097061922463) ^ 8032353974154 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 24097061922463) ^ 54 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_27317304886679 : Nat.Prime 27317304886679 := by
  apply lucas_primality 27317304886679 (11 : ZMod 27317304886679)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (118277, 1), (115480207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (118277, 1), (115480207, 1)] : List FactorBlock).map factorBlockValue).prod) = 27317304886679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_118277
      · exact prime_thirtyOneAC_115480207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 27317304886679) ^ 13658652443339 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 27317304886679) ^ 230960414 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 27317304886679) ^ 236554 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_32112913419533 : Nat.Prime 32112913419533 := by
  apply lucas_primality 32112913419533 (2 : ZMod 32112913419533)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (729838941353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (729838941353, 1)] : List FactorBlock).map factorBlockValue).prod) = 32112913419533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_729838941353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32112913419533) ^ 16056456709766 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32112913419533) ^ 2919355765412 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32112913419533) ^ 44 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_37659066478717 : Nat.Prime 37659066478717 := by
  apply lucas_primality 37659066478717 (5 : ZMod 37659066478717)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3138255539893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3138255539893, 1)] : List FactorBlock).map factorBlockValue).prod) = 37659066478717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_3138255539893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37659066478717) ^ 18829533239358 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 37659066478717) ^ 12553022159572 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 37659066478717) ^ 12 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_45819540753073 : Nat.Prime 45819540753073 := by
  apply lucas_primality 45819540753073 (5 : ZMod 45819540753073)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (103, 1), (298958273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (103, 1), (298958273, 1)] : List FactorBlock).map factorBlockValue).prod) = 45819540753073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_103
      · exact prime_thirtyOneAC_298958273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 45819540753073) ^ 22909770376536 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 45819540753073) ^ 15273180251024 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 45819540753073) ^ 1478049701712 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 45819540753073) ^ 444849910224 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 45819540753073) ^ 153264 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_48964745208143 : Nat.Prime 48964745208143 := by
  apply lucas_primality 48964745208143 (5 : ZMod 48964745208143)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (263, 1), (15647, 1), (5949311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (263, 1), (15647, 1), (5949311, 1)] : List FactorBlock).map factorBlockValue).prod) = 48964745208143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_263
      · exact prime_thirtyOneAC_15647
      · exact prime_thirtyOneAC_5949311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48964745208143) ^ 24482372604071 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 48964745208143) ^ 186177738434 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 48964745208143) ^ 3129337586 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 48964745208143) ^ 8230322 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_65434452607319 : Nat.Prime 65434452607319 := by
  apply lucas_primality 65434452607319 (11 : ZMod 65434452607319)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (2039, 1), (17690983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (2039, 1), (17690983, 1)] : List FactorBlock).map factorBlockValue).prod) = 65434452607319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_907
      · exact prime_thirtyOneAC_2039
      · exact prime_thirtyOneAC_17690983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 65434452607319) ^ 32717226303659 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 65434452607319) ^ 72143828674 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 65434452607319) ^ 32091443162 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 65434452607319) ^ 3698746 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_83056102444969 : Nat.Prime 83056102444969 := by
  apply lucas_primality 83056102444969 (14 : ZMod 83056102444969)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (111634546297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (111634546297, 1)] : List FactorBlock).map factorBlockValue).prod) = 83056102444969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_111634546297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 83056102444969) ^ 41528051222484 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (14 : ZMod 83056102444969) ^ 27685367481656 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (14 : ZMod 83056102444969) ^ 2679229111128 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (14 : ZMod 83056102444969) ^ 744 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_113029771412981 : Nat.Prime 113029771412981 := by
  apply lucas_primality 113029771412981 (2 : ZMod 113029771412981)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5651488570649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5651488570649, 1)] : List FactorBlock).map factorBlockValue).prod) = 113029771412981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_5651488570649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 113029771412981) ^ 56514885706490 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 113029771412981) ^ 22605954282596 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 113029771412981) ^ 20 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_133314707575871 : Nat.Prime 133314707575871 := by
  apply lucas_primality 133314707575871 (23 : ZMod 133314707575871)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (784204162211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (784204162211, 1)] : List FactorBlock).map factorBlockValue).prod) = 133314707575871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_784204162211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 133314707575871) ^ 66657353787935 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 133314707575871) ^ 26662941515174 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 133314707575871) ^ 7842041622110 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (23 : ZMod 133314707575871) ^ 170 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_142317349585973 : Nat.Prime 142317349585973 := by
  apply lucas_primality 142317349585973 (2 : ZMod 142317349585973)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (140629792081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (140629792081, 1)] : List FactorBlock).map factorBlockValue).prod) = 142317349585973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_140629792081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142317349585973) ^ 71158674792986 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 142317349585973) ^ 12937940871452 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 142317349585973) ^ 6187710851564 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 142317349585973) ^ 1012 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_195498806743621 : Nat.Prime 195498806743621 := by
  apply lucas_primality 195498806743621 (7 : ZMod 195498806743621)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (362034827303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (362034827303, 1)] : List FactorBlock).map factorBlockValue).prod) = 195498806743621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_362034827303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 195498806743621) ^ 97749403371810 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 195498806743621) ^ 65166268914540 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 195498806743621) ^ 39099761348724 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 195498806743621) ^ 540 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_218475249934771 : Nat.Prime 218475249934771 := by
  apply lucas_primality 218475249934771 (2 : ZMod 218475249934771)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (6197, 1), (130574083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (6197, 1), (130574083, 1)] : List FactorBlock).map factorBlockValue).prod) = 218475249934771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_6197
      · exact prime_thirtyOneAC_130574083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 218475249934771) ^ 109237624967385 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 218475249934771) ^ 72825083311590 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 218475249934771) ^ 43695049986954 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 218475249934771) ^ 35255002410 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 218475249934771) ^ 1673190 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_311663800781999 : Nat.Prime 311663800781999 := by
  apply lucas_primality 311663800781999 (7 : ZMod 311663800781999)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (22261700055857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (22261700055857, 1)] : List FactorBlock).map factorBlockValue).prod) = 311663800781999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_22261700055857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 311663800781999) ^ 155831900390999 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 311663800781999) ^ 44523400111714 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 311663800781999) ^ 14 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_466761419158829 : Nat.Prime 466761419158829 := by
  apply lucas_primality 466761419158829 (2 : ZMod 466761419158829)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (131, 1), (114451, 1), (338389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (131, 1), (114451, 1), (338389, 1)] : List FactorBlock).map factorBlockValue).prod) = 466761419158829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_131
      · exact prime_thirtyOneAC_114451
      · exact prime_thirtyOneAC_338389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 466761419158829) ^ 233380709579414 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 466761419158829) ^ 20293974746036 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 466761419158829) ^ 3563064268388 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 466761419158829) ^ 4078264228 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 466761419158829) ^ 1379363452 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_731913787141181 : Nat.Prime 731913787141181 := by
  apply lucas_primality 731913787141181 (3 : ZMod 731913787141181)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (5227955622437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (5227955622437, 1)] : List FactorBlock).map factorBlockValue).prod) = 731913787141181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_5227955622437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 731913787141181) ^ 365956893570590 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 731913787141181) ^ 146382757428236 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 731913787141181) ^ 104559112448740 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 731913787141181) ^ 140 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_933522838317659 : Nat.Prime 933522838317659 := by
  apply lucas_primality 933522838317659 (2 : ZMod 933522838317659)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (466761419158829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (466761419158829, 1)] : List FactorBlock).map factorBlockValue).prod) = 933522838317659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_466761419158829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 933522838317659) ^ 466761419158829 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 933522838317659) ^ 2 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1393417375684441 : Nat.Prime 1393417375684441 := by
  apply lucas_primality 1393417375684441 (11 : ZMod 1393417375684441)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (41, 1), (101, 1), (127, 1), (22079591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (41, 1), (101, 1), (127, 1), (22079591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1393417375684441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_101
      · exact prime_thirtyOneAC_127
      · exact prime_thirtyOneAC_22079591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1393417375684441) ^ 696708687842220 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1393417375684441) ^ 464472458561480 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1393417375684441) ^ 278683475136888 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1393417375684441) ^ 33985789650840 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1393417375684441) ^ 13796211640440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1393417375684441) ^ 10971790359720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1393417375684441) ^ 63108840 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1875129307657919 : Nat.Prime 1875129307657919 := by
  apply lucas_primality 1875129307657919 (11 : ZMod 1875129307657919)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (43, 2), (1747, 1), (1175099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (43, 2), (1747, 1), (1175099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1875129307657919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_1747
      · exact prime_thirtyOneAC_1175099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1875129307657919) ^ 937564653828959 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1875129307657919) ^ 144240715973686 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1875129307657919) ^ 98691016192522 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1875129307657919) ^ 43607658317626 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1875129307657919) ^ 1073342477194 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 1875129307657919) ^ 1595720282 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2071070973961349 : Nat.Prime 2071070973961349 := by
  apply lucas_primality 2071070973961349 (2 : ZMod 2071070973961349)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (131, 1), (179, 1), (3529, 1), (272039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (131, 1), (179, 1), (3529, 1), (272039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2071070973961349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_131
      · exact prime_thirtyOneAC_179
      · exact prime_thirtyOneAC_3529
      · exact prime_thirtyOneAC_272039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2071070973961349) ^ 1035535486980674 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2071070973961349) ^ 90046564085276 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2071070973961349) ^ 15809702091308 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2071070973961349) ^ 11570228904812 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2071070973961349) ^ 586871911012 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2071070973961349) ^ 7613139932 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2383361135673493 : Nat.Prime 2383361135673493 := by
  apply lucas_primality 2383361135673493 (2 : ZMod 2383361135673493)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (15277955997907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (15277955997907, 1)] : List FactorBlock).map factorBlockValue).prod) = 2383361135673493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_15277955997907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2383361135673493) ^ 1191680567836746 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2383361135673493) ^ 794453711891164 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2383361135673493) ^ 183335471974884 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2383361135673493) ^ 156 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2449512761802971 : Nat.Prime 2449512761802971 := by
  apply lucas_primality 2449512761802971 (2 : ZMod 2449512761802971)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (197, 1), (5521, 1), (13247893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (197, 1), (5521, 1), (13247893, 1)] : List FactorBlock).map factorBlockValue).prod) = 2449512761802971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_197
      · exact prime_thirtyOneAC_5521
      · exact prime_thirtyOneAC_13247893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2449512761802971) ^ 1224756380901485 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2449512761802971) ^ 489902552360594 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2449512761802971) ^ 144088985988410 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2449512761802971) ^ 12434074933010 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2449512761802971) ^ 443671936570 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2449512761802971) ^ 184898290 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2474255200665943 : Nat.Prime 2474255200665943 := by
  apply lucas_primality 2474255200665943 (5 : ZMod 2474255200665943)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (45819540753073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (45819540753073, 1)] : List FactorBlock).map factorBlockValue).prod) = 2474255200665943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_45819540753073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2474255200665943) ^ 1237127600332971 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 2474255200665943) ^ 824751733555314 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 2474255200665943) ^ 54 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3044187000170557 : Nat.Prime 3044187000170557 := by
  apply lucas_primality 3044187000170557 (2 : ZMod 3044187000170557)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (149, 1), (1702565436337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (149, 1), (1702565436337, 1)] : List FactorBlock).map factorBlockValue).prod) = 3044187000170557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_149
      · exact prime_thirtyOneAC_1702565436337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3044187000170557) ^ 1522093500085278 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3044187000170557) ^ 1014729000056852 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3044187000170557) ^ 20430785236044 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3044187000170557) ^ 1788 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3528133446039211 : Nat.Prime 3528133446039211 := by
  apply lucas_primality 3528133446039211 (3 : ZMod 3528133446039211)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1908041, 1), (20545409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1908041, 1), (20545409, 1)] : List FactorBlock).map factorBlockValue).prod) = 3528133446039211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_1908041
      · exact prime_thirtyOneAC_20545409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3528133446039211) ^ 1764066723019605 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3528133446039211) ^ 1176044482013070 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3528133446039211) ^ 705626689207842 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3528133446039211) ^ 1849086810 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 3528133446039211) ^ 171723690 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3664010351887681 : Nat.Prime 3664010351887681 := by
  apply lucas_primality 3664010351887681 (7 : ZMod 3664010351887681)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (23, 1), (47, 1), (257, 1), (269, 1), (51071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (23, 1), (47, 1), (257, 1), (269, 1), (51071, 1)] : List FactorBlock).map factorBlockValue).prod) = 3664010351887681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_257
      · exact prime_thirtyOneAC_269
      · exact prime_thirtyOneAC_51071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3664010351887681) ^ 1832005175943840 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 3664010351887681) ^ 1221336783962560 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 3664010351887681) ^ 732802070377536 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 3664010351887681) ^ 159304797908160 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 3664010351887681) ^ 77957667061440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 3664010351887681) ^ 14256849618240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 3664010351887681) ^ 13620856326720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 3664010351887681) ^ 71743462080 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4652851227829433 : Nat.Prime 4652851227829433 := by
  apply lucas_primality 4652851227829433 (3 : ZMod 4652851227829433)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (59, 1), (419, 1), (907, 1), (836747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (59, 1), (419, 1), (907, 1), (836747, 1)] : List FactorBlock).map factorBlockValue).prod) = 4652851227829433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_419
      · exact prime_thirtyOneAC_907
      · exact prime_thirtyOneAC_836747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4652851227829433) ^ 2326425613914716 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652851227829433) ^ 150091975091272 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652851227829433) ^ 78861885217448 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652851227829433) ^ 11104656868328 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652851227829433) ^ 5129935201576 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4652851227829433) ^ 5560642856 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_10758635434896721 : Nat.Prime 10758635434896721 := by
  apply lucas_primality 10758635434896721 (13 : ZMod 10758635434896721)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 2), (547, 1), (1672486201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 2), (547, 1), (1672486201, 1)] : List FactorBlock).map factorBlockValue).prod) = 10758635434896721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_547
      · exact prime_thirtyOneAC_1672486201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10758635434896721) ^ 5379317717448360 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 10758635434896721) ^ 3586211811632240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 10758635434896721) ^ 2151727086979344 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 10758635434896721) ^ 1536947919270960 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 10758635434896721) ^ 19668437723760 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 10758635434896721) ^ 6432720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_11729928404617261 : Nat.Prime 11729928404617261 := by
  apply lucas_primality 11729928404617261 (6 : ZMod 11729928404617261)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (195498806743621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (195498806743621, 1)] : List FactorBlock).map factorBlockValue).prod) = 11729928404617261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_195498806743621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 11729928404617261) ^ 5864964202308630 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 11729928404617261) ^ 3909976134872420 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 11729928404617261) ^ 2345985680923452 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 11729928404617261) ^ 60 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_11921818319404579 : Nat.Prime 11921818319404579 := by
  apply lucas_primality 11921818319404579 (2 : ZMod 11921818319404579)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (241, 1), (70467415679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (241, 1), (70467415679, 1)] : List FactorBlock).map factorBlockValue).prod) = 11921818319404579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_241
      · exact prime_thirtyOneAC_70467415679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11921818319404579) ^ 5960909159702289 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 11921818319404579) ^ 3973939439801526 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 11921818319404579) ^ 917062947646506 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 11921818319404579) ^ 49468125806658 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 11921818319404579) ^ 169182 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_12524358967375187 : Nat.Prime 12524358967375187 := by
  apply lucas_primality 12524358967375187 (2 : ZMod 12524358967375187)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (504299, 1), (12417592507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (504299, 1), (12417592507, 1)] : List FactorBlock).map factorBlockValue).prod) = 12524358967375187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_504299
      · exact prime_thirtyOneAC_12417592507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12524358967375187) ^ 6262179483687593 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 12524358967375187) ^ 24835185014 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 12524358967375187) ^ 1008598 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_12720632046923221 : Nat.Prime 12720632046923221 := by
  apply lucas_primality 12720632046923221 (31 : ZMod 12720632046923221)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (37, 1), (367, 1), (2230445479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (37, 1), (367, 1), (2230445479, 1)] : List FactorBlock).map factorBlockValue).prod) = 12720632046923221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_367
      · exact prime_thirtyOneAC_2230445479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 12720632046923221) ^ 6360316023461610 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 12720632046923221) ^ 4240210682307740 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 12720632046923221) ^ 2544126409384644 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 12720632046923221) ^ 1817233149560460 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 12720632046923221) ^ 343800866133060 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 12720632046923221) ^ 34661122743660 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (31 : ZMod 12720632046923221) ^ 5703180 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_16552192875913423 : Nat.Prime 16552192875913423 := by
  apply lucas_primality 16552192875913423 (3 : ZMod 16552192875913423)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 2), (13, 1), (41, 1), (61, 1), (64133863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 2), (13, 1), (41, 1), (61, 1), (64133863, 1)] : List FactorBlock).map factorBlockValue).prod) = 16552192875913423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_61
      · exact prime_thirtyOneAC_64133863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16552192875913423) ^ 8276096437956711 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 16552192875913423) ^ 5517397625304474 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 16552192875913423) ^ 2364598982273346 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 16552192875913423) ^ 1273245605839494 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 16552192875913423) ^ 403712021363742 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 16552192875913423) ^ 271347424195302 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 16552192875913423) ^ 258088194 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_20468092563622489 : Nat.Prime 20468092563622489 := by
  apply lucas_primality 20468092563622489 (13 : ZMod 20468092563622489)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (3083359, 1), (5884969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (3083359, 1), (5884969, 1)] : List FactorBlock).map factorBlockValue).prod) = 20468092563622489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_3083359
      · exact prime_thirtyOneAC_5884969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 20468092563622489) ^ 10234046281811244 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 20468092563622489) ^ 6822697521207496 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 20468092563622489) ^ 435491331140904 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 20468092563622489) ^ 6638245032 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 20468092563622489) ^ 3478028952 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_25021658269037819 : Nat.Prime 25021658269037819 := by
  apply lucas_primality 25021658269037819 (2 : ZMod 25021658269037819)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53367757, 1), (234426737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53367757, 1), (234426737, 1)] : List FactorBlock).map factorBlockValue).prod) = 25021658269037819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_53367757
      · exact prime_thirtyOneAC_234426737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25021658269037819) ^ 12510829134518909 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 25021658269037819) ^ 468853474 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 25021658269037819) ^ 106735514 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_29339214641414449 : Nat.Prime 29339214641414449 := by
  apply lucas_primality 29339214641414449 (13 : ZMod 29339214641414449)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (11813, 1), (2723287183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (11813, 1), (2723287183, 1)] : List FactorBlock).map factorBlockValue).prod) = 29339214641414449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_11813
      · exact prime_thirtyOneAC_2723287183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 29339214641414449) ^ 14669607320707224 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 29339214641414449) ^ 9779738213804816 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 29339214641414449) ^ 1544169191653392 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 29339214641414449) ^ 2483637910896 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 29339214641414449) ^ 10773456 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_32225767748647973 : Nat.Prime 32225767748647973 := by
  apply lucas_primality 32225767748647973 (2 : ZMod 32225767748647973)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (83056102444969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (83056102444969, 1)] : List FactorBlock).map factorBlockValue).prod) = 32225767748647973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_97
      · exact prime_thirtyOneAC_83056102444969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32225767748647973) ^ 16112883874323986 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32225767748647973) ^ 332224409779876 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 32225767748647973) ^ 388 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_39151145698669351 : Nat.Prime 39151145698669351 := by
  apply lucas_primality 39151145698669351 (3 : ZMod 39151145698669351)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 2), (3222316518409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 2), (3222316518409, 1)] : List FactorBlock).map factorBlockValue).prod) = 39151145698669351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_3222316518409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39151145698669351) ^ 19575572849334675 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 39151145698669351) ^ 13050381899556450 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 39151145698669351) ^ 7830229139733870 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 39151145698669351) ^ 12150 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_42378235847274163 : Nat.Prime 42378235847274163 := by
  apply lucas_primality 42378235847274163 (2 : ZMod 42378235847274163)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (31, 1), (1069, 1), (6257, 1), (3096659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (31, 1), (1069, 1), (6257, 1), (3096659, 1)] : List FactorBlock).map factorBlockValue).prod) = 42378235847274163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_1069
      · exact prime_thirtyOneAC_6257
      · exact prime_thirtyOneAC_3096659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42378235847274163) ^ 21189117923637081 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378235847274163) ^ 14126078615758054 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378235847274163) ^ 3852566895206742 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378235847274163) ^ 1367039866041102 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378235847274163) ^ 39642877312698 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378235847274163) ^ 6772932051666 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378235847274163) ^ 13685147718 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_100569094565484823 : Nat.Prime 100569094565484823 := by
  apply lucas_primality 100569094565484823 (3 : ZMod 100569094565484823)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113777, 1), (147319016681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113777, 1), (147319016681, 1)] : List FactorBlock).map factorBlockValue).prod) = 100569094565484823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_113777
      · exact prime_thirtyOneAC_147319016681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 100569094565484823) ^ 50284547282742411 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 100569094565484823) ^ 33523031521828274 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 100569094565484823) ^ 883914100086 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 100569094565484823) ^ 682662 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_107586354348967211 : Nat.Prime 107586354348967211 := by
  apply lucas_primality 107586354348967211 (2 : ZMod 107586354348967211)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10758635434896721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10758635434896721, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586354348967211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_10758635434896721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 107586354348967211) ^ 53793177174483605 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 107586354348967211) ^ 21517270869793442 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 107586354348967211) ^ 10 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_128943120786088589 : Nat.Prime 128943120786088589 := by
  apply lucas_primality 128943120786088589 (2 : ZMod 128943120786088589)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (22486379, 1), (204795599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (22486379, 1), (204795599, 1)] : List FactorBlock).map factorBlockValue).prod) = 128943120786088589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_22486379
      · exact prime_thirtyOneAC_204795599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 128943120786088589) ^ 64471560393044294 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 128943120786088589) ^ 18420445826584084 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 128943120786088589) ^ 5734276772 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 128943120786088589) ^ 629618612 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_130178437986031789 : Nat.Prime 130178437986031789 := by
  apply lucas_primality 130178437986031789 (6 : ZMod 130178437986031789)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (71, 1), (10193, 1), (318933089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (71, 1), (10193, 1), (318933089, 1)] : List FactorBlock).map factorBlockValue).prod) = 130178437986031789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_71
      · exact prime_thirtyOneAC_10193
      · exact prime_thirtyOneAC_318933089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 130178437986031789) ^ 65089218993015894 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 130178437986031789) ^ 43392812662010596 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 130178437986031789) ^ 2769753999702804 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 130178437986031789) ^ 1833499126563828 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 130178437986031789) ^ 12771356615916 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 130178437986031789) ^ 408168492 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_245666806856293507 : Nat.Prime 245666806856293507 := by
  apply lucas_primality 245666806856293507 (3 : ZMod 245666806856293507)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (31, 1), (547, 1), (236209, 1), (444449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (31, 1), (547, 1), (236209, 1), (444449, 1)] : List FactorBlock).map factorBlockValue).prod) = 245666806856293507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_547
      · exact prime_thirtyOneAC_236209
      · exact prime_thirtyOneAC_444449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 245666806856293507) ^ 122833403428146753 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 245666806856293507) ^ 81888935618764502 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 245666806856293507) ^ 10681165515491022 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 245666806856293507) ^ 7924735705041726 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 245666806856293507) ^ 449116648731798 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 245666806856293507) ^ 1040039993634 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 245666806856293507) ^ 552744649794 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_268138141898980037 : Nat.Prime 268138141898980037 := by
  apply lucas_primality 268138141898980037 (2 : ZMod 268138141898980037)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (3528133446039211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (3528133446039211, 1)] : List FactorBlock).map factorBlockValue).prod) = 268138141898980037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_3528133446039211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 268138141898980037) ^ 134069070949490018 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 268138141898980037) ^ 14112533784156844 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 268138141898980037) ^ 76 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_347944387157928053 : Nat.Prime 347944387157928053 := by
  apply lucas_primality 347944387157928053 (2 : ZMod 347944387157928053)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (141731, 1), (613740796223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (141731, 1), (613740796223, 1)] : List FactorBlock).map factorBlockValue).prod) = 347944387157928053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_141731
      · exact prime_thirtyOneAC_613740796223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 347944387157928053) ^ 173972193578964026 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 347944387157928053) ^ 2454963184892 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 347944387157928053) ^ 566924 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_396572836680015109 : Nat.Prime 396572836680015109 := by
  apply lucas_primality 396572836680015109 (10 : ZMod 396572836680015109)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (887, 1), (291829, 1), (1434497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (887, 1), (291829, 1), (1434497, 1)] : List FactorBlock).map factorBlockValue).prod) = 396572836680015109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_89
      · exact prime_thirtyOneAC_887
      · exact prime_thirtyOneAC_291829
      · exact prime_thirtyOneAC_1434497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 396572836680015109) ^ 198286418340007554 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 396572836680015109) ^ 132190945560005036 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 396572836680015109) ^ 4455874569438372 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 396572836680015109) ^ 447094517113884 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 396572836680015109) ^ 1358921960052 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 396572836680015109) ^ 276454280964 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_430273172518401097 : Nat.Prime 430273172518401097 := by
  apply lucas_primality 430273172518401097 (5 : ZMod 430273172518401097)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (2179, 1), (37493, 1), (2709197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (2179, 1), (37493, 1), (2709197, 1)] : List FactorBlock).map factorBlockValue).prod) = 430273172518401097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_2179
      · exact prime_thirtyOneAC_37493
      · exact prime_thirtyOneAC_2709197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 430273172518401097) ^ 215136586259200548 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 430273172518401097) ^ 143424390839467032 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 430273172518401097) ^ 197463594547224 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 430273172518401097) ^ 11476093471272 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 430273172518401097) ^ 158819448168 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_458098944551652511 : Nat.Prime 458098944551652511 := by
  apply lucas_primality 458098944551652511 (3 : ZMod 458098944551652511)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (5446879, 1), (311492647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (5446879, 1), (311492647, 1)] : List FactorBlock).map factorBlockValue).prod) = 458098944551652511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_5446879
      · exact prime_thirtyOneAC_311492647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 458098944551652511) ^ 229049472275826255 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 458098944551652511) ^ 152699648183884170 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 458098944551652511) ^ 91619788910330502 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 458098944551652511) ^ 84103014690 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 458098944551652511) ^ 1470657330 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_503099215085633879 : Nat.Prime 503099215085633879 := by
  apply lucas_primality 503099215085633879 (11 : ZMod 503099215085633879)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (32135093, 1), (166550609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (32135093, 1), (166550609, 1)] : List FactorBlock).map factorBlockValue).prod) = 503099215085633879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_32135093
      · exact prime_thirtyOneAC_166550609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 503099215085633879) ^ 251549607542816939 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 503099215085633879) ^ 10704238618843274 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 503099215085633879) ^ 15655757246 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 503099215085633879) ^ 3020698742 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_519790568028711403 : Nat.Prime 519790568028711403 := by
  apply lucas_primality 519790568028711403 (2 : ZMod 519790568028711403)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (67, 1), (991, 1), (4651, 1), (4754779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (67, 1), (991, 1), (4651, 1), (4754779, 1)] : List FactorBlock).map factorBlockValue).prod) = 519790568028711403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_67
      · exact prime_thirtyOneAC_991
      · exact prime_thirtyOneAC_4651
      · exact prime_thirtyOneAC_4754779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 519790568028711403) ^ 259895284014355701 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 519790568028711403) ^ 173263522676237134 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 519790568028711403) ^ 8810009627605278 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 519790568028711403) ^ 7758068179533006 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 519790568028711403) ^ 524511168545622 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 519790568028711403) ^ 111758883687102 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 519790568028711403) ^ 109319606238 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_550838110474311931 : Nat.Prime 550838110474311931 := by
  apply lucas_primality 550838110474311931 (2 : ZMod 550838110474311931)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (107, 1), (7129, 1), (2674532153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (107, 1), (7129, 1), (2674532153, 1)] : List FactorBlock).map factorBlockValue).prod) = 550838110474311931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_107
      · exact prime_thirtyOneAC_7129
      · exact prime_thirtyOneAC_2674532153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 550838110474311931) ^ 275419055237155965 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 550838110474311931) ^ 183612703491437310 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 550838110474311931) ^ 110167622094862386 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 550838110474311931) ^ 5148019724058990 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 550838110474311931) ^ 77267233900170 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 550838110474311931) ^ 205956810 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_61717
      · exact prime_thirtyOneAC_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_640079815404794459 : Nat.Prime 640079815404794459 := by
  apply lucas_primality 640079815404794459 (2 : ZMod 640079815404794459)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (73, 1), (65434452607319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (73, 1), (65434452607319, 1)] : List FactorBlock).map factorBlockValue).prod) = 640079815404794459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_67
      · exact prime_thirtyOneAC_73
      · exact prime_thirtyOneAC_65434452607319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 640079815404794459) ^ 320039907702397229 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 640079815404794459) ^ 9553430080668574 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 640079815404794459) ^ 8768216649380746 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 640079815404794459) ^ 9782 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_869555297020315813 : Nat.Prime 869555297020315813 := by
  apply lucas_primality 869555297020315813 (5 : ZMod 869555297020315813)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (167, 1), (181, 1), (126173256427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (167, 1), (181, 1), (126173256427, 1)] : List FactorBlock).map factorBlockValue).prod) = 869555297020315813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_167
      · exact prime_thirtyOneAC_181
      · exact prime_thirtyOneAC_126173256427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 869555297020315813) ^ 434777648510157906 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 869555297020315813) ^ 289851765673438604 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 869555297020315813) ^ 45766068264227148 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 869555297020315813) ^ 5206917946229436 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 869555297020315813) ^ 4804172911714452 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 869555297020315813) ^ 6891756 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_947616752192632807 : Nat.Prime 947616752192632807 := by
  apply lucas_primality 947616752192632807 (3 : ZMod 947616752192632807)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2273, 1), (211727, 1), (328175231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2273, 1), (211727, 1), (328175231, 1)] : List FactorBlock).map factorBlockValue).prod) = 947616752192632807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_2273
      · exact prime_thirtyOneAC_211727
      · exact prime_thirtyOneAC_328175231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 947616752192632807) ^ 473808376096316403 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 947616752192632807) ^ 315872250730877602 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 947616752192632807) ^ 416901342803622 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 947616752192632807) ^ 4475653800378 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 947616752192632807) ^ 2887532826 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1046688674750338177 : Nat.Prime 1046688674750338177 := by
  apply lucas_primality 1046688674750338177 (5 : ZMod 1046688674750338177)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (523, 1), (4817, 1), (120216881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (523, 1), (4817, 1), (120216881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1046688674750338177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_523
      · exact prime_thirtyOneAC_4817
      · exact prime_thirtyOneAC_120216881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1046688674750338177) ^ 523344337375169088 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046688674750338177) ^ 348896224916779392 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046688674750338177) ^ 2001316777725312 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046688674750338177) ^ 217290569804928 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 1046688674750338177) ^ 8706669696 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1678556719318268747 : Nat.Prime 1678556719318268747 := by
  apply lucas_primality 1678556719318268747 (2 : ZMod 1678556719318268747)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4651, 1), (16404651192493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4651, 1), (16404651192493, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678556719318268747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_4651
      · exact prime_thirtyOneAC_16404651192493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1678556719318268747) ^ 839278359659134373 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678556719318268747) ^ 152596065392569886 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678556719318268747) ^ 360902326234846 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1678556719318268747) ^ 102322 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1721092690073604389 : Nat.Prime 1721092690073604389 := by
  apply lucas_primality 1721092690073604389 (2 : ZMod 1721092690073604389)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (430273172518401097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (430273172518401097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1721092690073604389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_430273172518401097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1721092690073604389) ^ 860546345036802194 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1721092690073604389) ^ 4 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2690071001472801293 : Nat.Prime 2690071001472801293 := by
  apply lucas_primality 2690071001472801293 (2 : ZMod 2690071001472801293)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (449, 1), (15937, 1), (33589, 1), (39409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (449, 1), (15937, 1), (33589, 1), (39409, 1)] : List FactorBlock).map factorBlockValue).prod) = 2690071001472801293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_71
      · exact prime_thirtyOneAC_449
      · exact prime_thirtyOneAC_15937
      · exact prime_thirtyOneAC_33589
      · exact prime_thirtyOneAC_39409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2690071001472801293) ^ 1345035500736400646 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690071001472801293) ^ 37888323964405652 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690071001472801293) ^ 5991249446487308 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690071001472801293) ^ 168794064219916 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690071001472801293) ^ 80087856187228 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690071001472801293) ^ 68260321283788 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3867092129837756761 : Nat.Prime 3867092129837756761 := by
  apply lucas_primality 3867092129837756761 (11 : ZMod 3867092129837756761)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (32225767748647973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (32225767748647973, 1)] : List FactorBlock).map factorBlockValue).prod) = 3867092129837756761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_32225767748647973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3867092129837756761) ^ 1933546064918878380 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 3867092129837756761) ^ 1289030709945918920 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 3867092129837756761) ^ 773418425967551352 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 3867092129837756761) ^ 120 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4834452222109548047 : Nat.Prime 4834452222109548047 := by
  apply lucas_primality 4834452222109548047 (5 : ZMod 4834452222109548047)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (227, 1), (257, 1), (1289423, 1), (1890227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (227, 1), (257, 1), (1289423, 1), (1890227, 1)] : List FactorBlock).map factorBlockValue).prod) = 4834452222109548047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_227
      · exact prime_thirtyOneAC_257
      · exact prime_thirtyOneAC_1289423
      · exact prime_thirtyOneAC_1890227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4834452222109548047) ^ 2417226111054774023 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4834452222109548047) ^ 284379542477032238 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4834452222109548047) ^ 21297146352905498 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4834452222109548047) ^ 18811098140504078 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4834452222109548047) ^ 3749314400402 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4834452222109548047) ^ 2557604045498 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4926828424302554881 : Nat.Prime 4926828424302554881 := by
  apply lucas_primality 4926828424302554881 (13 : ZMod 4926828424302554881)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (11, 1), (563, 1), (2281, 1), (90825929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (11, 1), (563, 1), (2281, 1), (90825929, 1)] : List FactorBlock).map factorBlockValue).prod) = 4926828424302554881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_563
      · exact prime_thirtyOneAC_2281
      · exact prime_thirtyOneAC_90825929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 4926828424302554881) ^ 2463414212151277440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 4926828424302554881) ^ 1642276141434184960 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 4926828424302554881) ^ 985365684860510976 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 4926828424302554881) ^ 447893493118414080 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 4926828424302554881) ^ 8751027396629760 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 4926828424302554881) ^ 2159942316660480 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 4926828424302554881) ^ 54244734720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_7977339719811275201 : Nat.Prime 7977339719811275201 := by
  apply lucas_primality 7977339719811275201 (3 : ZMod 7977339719811275201)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (6169993, 1), (808078279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (6169993, 1), (808078279, 1)] : List FactorBlock).map factorBlockValue).prod) = 7977339719811275201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_6169993
      · exact prime_thirtyOneAC_808078279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7977339719811275201) ^ 3988669859905637600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 7977339719811275201) ^ 1595467943962255040 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 7977339719811275201) ^ 1292925246400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 7977339719811275201) ^ 9871988800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_10466886747503381771 : Nat.Prime 10466886747503381771 := by
  apply lucas_primality 10466886747503381771 (2 : ZMod 10466886747503381771)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1046688674750338177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1046688674750338177, 1)] : List FactorBlock).map factorBlockValue).prod) = 10466886747503381771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_1046688674750338177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10466886747503381771) ^ 5233443373751690885 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 10466886747503381771) ^ 2093377349500676354 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 10466886747503381771) ^ 10 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_14173768429869541607 : Nat.Prime 14173768429869541607 := by
  apply lucas_primality 14173768429869541607 (5 : ZMod 14173768429869541607)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (29, 1), (749923, 1), (14168139683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (29, 1), (749923, 1), (14168139683, 1)] : List FactorBlock).map factorBlockValue).prod) = 14173768429869541607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_749923
      · exact prime_thirtyOneAC_14168139683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14173768429869541607) ^ 7086884214934770803 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 14173768429869541607) ^ 616250801298675722 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 14173768429869541607) ^ 488750635512742814 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 14173768429869541607) ^ 18900298337122 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 14173768429869541607) ^ 1000397282 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_15989359927390284359 : Nat.Prime 15989359927390284359 := by
  apply lucas_primality 15989359927390284359 (11 : ZMod 15989359927390284359)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (23, 1), (1033, 1), (46747, 1), (5498947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (23, 1), (1033, 1), (46747, 1), (5498947, 1)] : List FactorBlock).map factorBlockValue).prod) = 15989359927390284359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_1033
      · exact prime_thirtyOneAC_46747
      · exact prime_thirtyOneAC_5498947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 15989359927390284359) ^ 7994679963695142179 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 15989359927390284359) ^ 2284194275341469194 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 15989359927390284359) ^ 1453578175217298578 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 15989359927390284359) ^ 940550583964134374 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 15989359927390284359) ^ 695189562060447146 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 15989359927390284359) ^ 15478567209477526 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 15989359927390284359) ^ 342040343281714 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (11 : ZMod 15989359927390284359) ^ 2907713045314 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_55766244496350167293 : Nat.Prime 55766244496350167293 := by
  apply lucas_primality 55766244496350167293 (2 : ZMod 55766244496350167293)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (239, 1), (218475249934771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (239, 1), (218475249934771, 1)] : List FactorBlock).map factorBlockValue).prod) = 55766244496350167293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_89
      · exact prime_thirtyOneAC_239
      · exact prime_thirtyOneAC_218475249934771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55766244496350167293) ^ 27883122248175083646 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55766244496350167293) ^ 18588748165450055764 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55766244496350167293) ^ 626587016812923228 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55766244496350167293) ^ 233331566930335428 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 55766244496350167293) ^ 255252 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_62064910601561039047 : Nat.Prime 62064910601561039047 := by
  apply lucas_primality 62064910601561039047 (6 : ZMod 62064910601561039047)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (83, 1), (97, 1), (249133, 1), (736742561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (83, 1), (97, 1), (249133, 1), (736742561, 1)] : List FactorBlock).map factorBlockValue).prod) = 62064910601561039047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_83
      · exact prime_thirtyOneAC_97
      · exact prime_thirtyOneAC_249133
      · exact prime_thirtyOneAC_736742561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 62064910601561039047) ^ 31032455300780519523 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62064910601561039047) ^ 20688303533853679682 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62064910601561039047) ^ 8866415800223005578 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62064910601561039047) ^ 747770007247723362 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62064910601561039047) ^ 639844439191350918 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62064910601561039047) ^ 249123603061662 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 62064910601561039047) ^ 84242330886 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_176290723501195820807 : Nat.Prime 176290723501195820807 := by
  apply lucas_primality 176290723501195820807 (5 : ZMod 176290723501195820807)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (122069, 1), (256307, 1), (2817303341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (122069, 1), (256307, 1), (2817303341, 1)] : List FactorBlock).map factorBlockValue).prod) = 176290723501195820807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_122069
      · exact prime_thirtyOneAC_256307
      · exact prime_thirtyOneAC_2817303341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 176290723501195820807) ^ 88145361750597910403 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 176290723501195820807) ^ 1444189134843374 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 176290723501195820807) ^ 687810803065058 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 176290723501195820807) ^ 62574278366 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_223528563048523659397 : Nat.Prime 223528563048523659397 := by
  apply lucas_primality 223528563048523659397 (5 : ZMod 223528563048523659397)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (211, 1), (3044187000170557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (211, 1), (3044187000170557, 1)] : List FactorBlock).map factorBlockValue).prod) = 223528563048523659397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_211
      · exact prime_thirtyOneAC_3044187000170557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 223528563048523659397) ^ 111764281524261829698 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 223528563048523659397) ^ 74509521016174553132 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 223528563048523659397) ^ 7707881484431850324 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 223528563048523659397) ^ 1059377076059353836 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 223528563048523659397) ^ 73428 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2218979990470716935453 : Nat.Prime 2218979990470716935453 := by
  apply lucas_primality 2218979990470716935453 (2 : ZMod 2218979990470716935453)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (10466886747503381771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (10466886747503381771, 1)] : List FactorBlock).map factorBlockValue).prod) = 2218979990470716935453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_10466886747503381771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2218979990470716935453) ^ 1109489995235358467726 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2218979990470716935453) ^ 41867546990013527084 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 2218979990470716935453) ^ 212 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_107
      · exact prime_thirtyOneAC_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3173233023021524774527 : Nat.Prime 3173233023021524774527 := by
  apply lucas_primality 3173233023021524774527 (13 : ZMod 3173233023021524774527)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (176290723501195820807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (176290723501195820807, 1)] : List FactorBlock).map factorBlockValue).prod) = 3173233023021524774527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_176290723501195820807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3173233023021524774527) ^ 1586616511510762387263 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 3173233023021524774527) ^ 1057744341007174924842 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 3173233023021524774527) ^ 18 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4063584072952319855993 : Nat.Prime 4063584072952319855993 := by
  apply lucas_primality 4063584072952319855993 (3 : ZMod 4063584072952319855993)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (419, 1), (65539, 1), (1422859692403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (419, 1), (65539, 1), (1422859692403, 1)] : List FactorBlock).map factorBlockValue).prod) = 4063584072952319855993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_419
      · exact prime_thirtyOneAC_65539
      · exact prime_thirtyOneAC_1422859692403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4063584072952319855993) ^ 2031792036476159927996 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4063584072952319855993) ^ 312583390227101527384 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4063584072952319855993) ^ 9698291343561622568 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4063584072952319855993) ^ 62002533956153128 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 4063584072952319855993) ^ 2855927464 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_4614121145797648476697 : Nat.Prime 4614121145797648476697 := by
  apply lucas_primality 4614121145797648476697 (5 : ZMod 4614121145797648476697)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (239, 1), (268138141898980037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (239, 1), (268138141898980037, 1)] : List FactorBlock).map factorBlockValue).prod) = 4614121145797648476697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_239
      · exact prime_thirtyOneAC_268138141898980037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4614121145797648476697) ^ 2307060572898824238348 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4614121145797648476697) ^ 1538040381932549492232 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4614121145797648476697) ^ 19305946216726562664 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 4614121145797648476697) ^ 17208 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_14304287354084669154977 : Nat.Prime 14304287354084669154977 := by
  apply lucas_primality 14304287354084669154977 (3 : ZMod 14304287354084669154977)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (43, 1), (106649, 1), (1989275456551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (43, 1), (106649, 1), (1989275456551, 1)] : List FactorBlock).map factorBlockValue).prod) = 14304287354084669154977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_106649
      · exact prime_thirtyOneAC_1989275456551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14304287354084669154977) ^ 7152143677042334577488 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 14304287354084669154977) ^ 2043469622012095593568 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 14304287354084669154977) ^ 332657845443829515232 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 14304287354084669154977) ^ 134124908382494624 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 14304287354084669154977) ^ 7190702176 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_15560832596914813162223 : Nat.Prime 15560832596914813162223 := by
  apply lucas_primality 15560832596914813162223 (5 : ZMod 15560832596914813162223)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2354202161, 1), (3304905766951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2354202161, 1), (3304905766951, 1)] : List FactorBlock).map factorBlockValue).prod) = 15560832596914813162223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_2354202161
      · exact prime_thirtyOneAC_3304905766951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15560832596914813162223) ^ 7780416298457406581111 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 15560832596914813162223) ^ 6609811533902 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 15560832596914813162223) ^ 4708404322 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_53383721082971361329867 : Nat.Prime 53383721082971361329867 := by
  apply lucas_primality 53383721082971361329867 (2 : ZMod 53383721082971361329867)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (200216923, 1), (133314707575871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (200216923, 1), (133314707575871, 1)] : List FactorBlock).map factorBlockValue).prod) = 53383721082971361329867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_200216923
      · exact prime_thirtyOneAC_133314707575871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53383721082971361329867) ^ 26691860541485680664933 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 53383721082971361329867) ^ 266629415151742 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 53383721082971361329867) ^ 400433846 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_64171845153858056601863 : Nat.Prime 64171845153858056601863 := by
  apply lucas_primality 64171845153858056601863 (5 : ZMod 64171845153858056601863)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (43, 1), (877, 1), (29339214641414449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (43, 1), (877, 1), (29339214641414449, 1)] : List FactorBlock).map factorBlockValue).prod) = 64171845153858056601863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_877
      · exact prime_thirtyOneAC_29339214641414449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 64171845153858056601863) ^ 32085922576929028300931 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 64171845153858056601863) ^ 2212822246684760572478 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 64171845153858056601863) ^ 1492368491950187362834 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 64171845153858056601863) ^ 73172001315687635806 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 64171845153858056601863) ^ 2187238 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_74061454194772068820769 : Nat.Prime 74061454194772068820769 := by
  apply lucas_primality 74061454194772068820769 (6 : ZMod 74061454194772068820769)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (71, 1), (397, 1), (11729928404617261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (71, 1), (397, 1), (11729928404617261, 1)] : List FactorBlock).map factorBlockValue).prod) = 74061454194772068820769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_71
      · exact prime_thirtyOneAC_397
      · exact prime_thirtyOneAC_11729928404617261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 74061454194772068820769) ^ 37030727097386034410384 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 74061454194772068820769) ^ 10580207742110295545824 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 74061454194772068820769) ^ 1043119073165803786208 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 74061454194772068820769) ^ 186552781347032918944 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 74061454194772068820769) ^ 6313888 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_76851066066654414537329 : Nat.Prime 76851066066654414537329 := by
  apply lucas_primality 76851066066654414537329 (3 : ZMod 76851066066654414537329)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (113341, 1), (42378235847274163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (113341, 1), (42378235847274163, 1)] : List FactorBlock).map factorBlockValue).prod) = 76851066066654414537329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_113341
      · exact prime_thirtyOneAC_42378235847274163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 76851066066654414537329) ^ 38425533033327207268664 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 76851066066654414537329) ^ 678051773556386608 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 76851066066654414537329) ^ 1813456 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_78358258999774420319657 : Nat.Prime 78358258999774420319657 := by
  apply lucas_primality 78358258999774420319657 (3 : ZMod 78358258999774420319657)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3440996113, 1), (2846496204389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3440996113, 1), (2846496204389, 1)] : List FactorBlock).map factorBlockValue).prod) = 78358258999774420319657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3440996113
      · exact prime_thirtyOneAC_2846496204389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 78358258999774420319657) ^ 39179129499887210159828 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 78358258999774420319657) ^ 22771969635112 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 78358258999774420319657) ^ 27527968904 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_90558899679741372365663 : Nat.Prime 90558899679741372365663 := by
  apply lucas_primality 90558899679741372365663 (5 : ZMod 90558899679741372365663)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (53717, 1), (2071070973961349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (53717, 1), (2071070973961349, 1)] : List FactorBlock).map factorBlockValue).prod) = 90558899679741372365663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_53717
      · exact prime_thirtyOneAC_2071070973961349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 90558899679741372365663) ^ 45279449839870686182831 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 90558899679741372365663) ^ 8232627243612852033242 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 90558899679741372365663) ^ 2447537829182199253126 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 90558899679741372365663) ^ 1685851772804538086 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 90558899679741372365663) ^ 43725638 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_106249614886974706961551 : Nat.Prime 106249614886974706961551 := by
  apply lucas_primality 106249614886974706961551 (3 : ZMod 106249614886974706961551)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (887, 1), (113053243, 1), (642150427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (887, 1), (113053243, 1), (642150427, 1)] : List FactorBlock).map factorBlockValue).prod) = 106249614886974706961551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_887
      · exact prime_thirtyOneAC_113053243
      · exact prime_thirtyOneAC_642150427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 106249614886974706961551) ^ 53124807443487353480775 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 106249614886974706961551) ^ 35416538295658235653850 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 106249614886974706961551) ^ 21249922977394941392310 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 106249614886974706961551) ^ 9659055898815882451050 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 106249614886974706961551) ^ 119785360639204855650 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 106249614886974706961551) ^ 939819257435850 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 106249614886974706961551) ^ 165459073792650 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_148703764863925873015853 : Nat.Prime 148703764863925873015853 := by
  apply lucas_primality 148703764863925873015853 (2 : ZMod 148703764863925873015853)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (1933, 1), (519790568028711403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (1933, 1), (519790568028711403, 1)] : List FactorBlock).map factorBlockValue).prod) = 148703764863925873015853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_1933
      · exact prime_thirtyOneAC_519790568028711403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 148703764863925873015853) ^ 74351882431962936507926 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 148703764863925873015853) ^ 4019020671997996567996 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 148703764863925873015853) ^ 76929004068249287644 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 148703764863925873015853) ^ 286084 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_163181655256001791168453 : Nat.Prime 163181655256001791168453 := by
  apply lucas_primality 163181655256001791168453 (2 : ZMod 163181655256001791168453)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (197, 1), (260747, 1), (3438062887697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (197, 1), (260747, 1), (3438062887697, 1)] : List FactorBlock).map factorBlockValue).prod) = 163181655256001791168453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_197
      · exact prime_thirtyOneAC_260747
      · exact prime_thirtyOneAC_3438062887697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 163181655256001791168453) ^ 81590827628000895584226 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 163181655256001791168453) ^ 54393885085333930389484 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 163181655256001791168453) ^ 23311665036571684452636 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 163181655256001791168453) ^ 14834695932363799197132 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 163181655256001791168453) ^ 828333275411176604916 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 163181655256001791168453) ^ 625823711321709516 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 163181655256001791168453) ^ 47463254916 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_170702195158835648746651 : Nat.Prime 170702195158835648746651 := by
  apply lucas_primality 170702195158835648746651 (2 : ZMod 170702195158835648746651)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (71, 1), (3580229, 1), (497434820581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (71, 1), (3580229, 1), (497434820581, 1)] : List FactorBlock).map factorBlockValue).prod) = 170702195158835648746651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_71
      · exact prime_thirtyOneAC_3580229
      · exact prime_thirtyOneAC_497434820581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170702195158835648746651) ^ 85351097579417824373325 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 170702195158835648746651) ^ 56900731719611882915550 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 170702195158835648746651) ^ 34140439031767129749330 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 170702195158835648746651) ^ 2404256269842755616150 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 170702195158835648746651) ^ 47679127552688850 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 170702195158835648746651) ^ 343164949650 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_317329374239692199667973 : Nat.Prime 317329374239692199667973 := by
  apply lucas_primality 317329374239692199667973 (2 : ZMod 317329374239692199667973)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (151, 1), (2333, 1), (25021658269037819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (151, 1), (2333, 1), (25021658269037819, 1)] : List FactorBlock).map factorBlockValue).prod) = 317329374239692199667973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_151
      · exact prime_thirtyOneAC_2333
      · exact prime_thirtyOneAC_25021658269037819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 317329374239692199667973) ^ 158664687119846099833986 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 317329374239692199667973) ^ 105776458079897399889324 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 317329374239692199667973) ^ 2101519034699948342172 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 317329374239692199667973) ^ 136017734350489584084 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 317329374239692199667973) ^ 12682188 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_336939649246947710784307 : Nat.Prime 336939649246947710784307 := by
  apply lucas_primality 336939649246947710784307 (7 : ZMod 336939649246947710784307)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (53, 1), (55766244496350167293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (53, 1), (55766244496350167293, 1)] : List FactorBlock).map factorBlockValue).prod) = 336939649246947710784307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_55766244496350167293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 336939649246947710784307) ^ 168469824623473855392153 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 336939649246947710784307) ^ 112313216415649236928102 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 336939649246947710784307) ^ 17733665749839353199174 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 336939649246947710784307) ^ 6357351872583919071402 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (7 : ZMod 336939649246947710784307) ^ 6042 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_440296412868662785834361 : Nat.Prime 440296412868662785834361 := by
  apply lucas_primality 440296412868662785834361 (6 : ZMod 440296412868662785834361)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (7573, 1), (32174563, 1), (3475051057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (7573, 1), (32174563, 1), (3475051057, 1)] : List FactorBlock).map factorBlockValue).prod) = 440296412868662785834361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_7573
      · exact prime_thirtyOneAC_32174563
      · exact prime_thirtyOneAC_3475051057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 440296412868662785834361) ^ 220148206434331392917180 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 440296412868662785834361) ^ 88059282573732557166872 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 440296412868662785834361) ^ 33868954836050983525720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 440296412868662785834361) ^ 58140289564064807320 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 440296412868662785834361) ^ 13684612060423720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (6 : ZMod 440296412868662785834361) ^ 126702142111480 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1319209322841677715529919 : Nat.Prime 1319209322841677715529919 := by
  apply lucas_primality 1319209322841677715529919 (13 : ZMod 1319209322841677715529919)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (269, 1), (14173768429869541607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (269, 1), (14173768429869541607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1319209322841677715529919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_173
      · exact prime_thirtyOneAC_269
      · exact prime_thirtyOneAC_14173768429869541607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1319209322841677715529919) ^ 659604661420838857764959 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 1319209322841677715529919) ^ 7625487415269813384566 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 1319209322841677715529919) ^ 4904123876734861396022 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (13 : ZMod 1319209322841677715529919) ^ 93074 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_1916454371846239818701747 : Nat.Prime 1916454371846239818701747 := by
  apply lucas_primality 1916454371846239818701747 (2 : ZMod 1916454371846239818701747)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (31, 1), (1721, 1), (163159471, 1), (10007392883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (31, 1), (1721, 1), (163159471, 1), (10007392883, 1)] : List FactorBlock).map factorBlockValue).prod) = 1916454371846239818701747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_1721
      · exact prime_thirtyOneAC_163159471
      · exact prime_thirtyOneAC_10007392883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1916454371846239818701747) ^ 958227185923119909350873 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1916454371846239818701747) ^ 174223124713294528972886 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1916454371846239818701747) ^ 61821108769233542538766 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1916454371846239818701747) ^ 1113570233495781417026 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1916454371846239818701747) ^ 11745897189420526 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 1916454371846239818701747) ^ 191503860621062 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3014250629754707648067457 : Nat.Prime 3014250629754707648067457 := by
  apply lucas_primality 3014250629754707648067457 (10 : ZMod 3014250629754707648067457)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (127, 1), (912832351, 1), (22570030039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (127, 1), (912832351, 1), (22570030039, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014250629754707648067457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_127
      · exact prime_thirtyOneAC_912832351
      · exact prime_thirtyOneAC_22570030039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3014250629754707648067457) ^ 1507125314877353824033728 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3014250629754707648067457) ^ 1004750209918235882689152 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3014250629754707648067457) ^ 23734256927202422425728 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3014250629754707648067457) ^ 3302085674825856 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (10 : ZMod 3014250629754707648067457) ^ 133551024280704 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3186426135210179994162077 : Nat.Prime 3186426135210179994162077 := by
  apply lucas_primality 3186426135210179994162077 (2 : ZMod 3186426135210179994162077)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (3109, 1), (4834452222109548047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (3109, 1), (4834452222109548047, 1)] : List FactorBlock).map factorBlockValue).prod) = 3186426135210179994162077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_3109
      · exact prime_thirtyOneAC_4834452222109548047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3186426135210179994162077) ^ 1593213067605089997081038 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3186426135210179994162077) ^ 60121247834154339512492 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3186426135210179994162077) ^ 1024903871087224185964 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3186426135210179994162077) ^ 659108 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3842553303332720726866451 : Nat.Prime 3842553303332720726866451 := by
  apply lucas_primality 3842553303332720726866451 (2 : ZMod 3842553303332720726866451)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (76851066066654414537329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (76851066066654414537329, 1)] : List FactorBlock).map factorBlockValue).prod) = 3842553303332720726866451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_76851066066654414537329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3842553303332720726866451) ^ 1921276651666360363433225 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842553303332720726866451) ^ 768510660666544145373290 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 3842553303332720726866451) ^ 50 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_6520240776941378810327737 : Nat.Prime 6520240776941378810327737 := by
  apply lucas_primality 6520240776941378810327737 (5 : ZMod 6520240776941378810327737)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (90558899679741372365663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (90558899679741372365663, 1)] : List FactorBlock).map factorBlockValue).prod) = 6520240776941378810327737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_90558899679741372365663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6520240776941378810327737) ^ 3260120388470689405163868 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 6520240776941378810327737) ^ 2173413592313792936775912 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (5 : ZMod 6520240776941378810327737) ^ 72 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_13380895730992146875813147 : Nat.Prime 13380895730992146875813147 := by
  apply lucas_primality 13380895730992146875813147 (2 : ZMod 13380895730992146875813147)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (163181655256001791168453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (163181655256001791168453, 1)] : List FactorBlock).map factorBlockValue).prod) = 13380895730992146875813147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_163181655256001791168453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13380895730992146875813147) ^ 6690447865496073437906573 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 13380895730992146875813147) ^ 326363310512003582336906 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (2 : ZMod 13380895730992146875813147) ^ 82 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_373982381705994798906655201 : Nat.Prime 373982381705994798906655201 := by
  apply lucas_primality 373982381705994798906655201 (83 : ZMod 373982381705994798906655201)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 373982381705994798906655201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 373982381705994798906655201) ^ 186991190852997399453327600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 124660793901998266302218400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 74796476341198959781331040 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 33998398336908618082423200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 28767875515845753762050400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 21998963629764399935685600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 19683283247683936784560800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 16260103552434556474202400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 12895944196758441341608800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 12063947796967574158279200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 10107631937999859429909600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 9121521505024263387967200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 8697264690837088346666400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 7957071951191378700141600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 7056271352943298092578400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 6338684435694827100112800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 373982381705994798906655201) ^ 6130858716491718014863200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_398372537034646633617958801 : Nat.Prime 398372537034646633617958801 := by
  apply lucas_primality 398372537034646633617958801 (71 : ZMod 398372537034646633617958801)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 398372537034646633617958801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 398372537034646633617958801) ^ 199186268517323316808979400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 132790845678215544539319600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 79674507406929326723591760 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 56910362433520947659708400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 36215685184967875783450800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 30644041310357433355227600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 23433678649096860801056400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 20966975633402454400945200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 13736984035677470124757200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 12850727001117633342514800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 10766825325260719827512400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 9716403342308454478486800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 9264477605456898456231600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 8476011426269077311020400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 7516462962917861011659600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 6752076898892315824033200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (71 : ZMod 398372537034646633617958801) ^ 6530697328436830059310800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_411800824799859441492721457 : Nat.Prime 411800824799859441492721457 := by
  apply lucas_primality 411800824799859441492721457 (3 : ZMod 411800824799859441492721457)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (6655531, 1), (3867092129837756761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (6655531, 1), (3867092129837756761, 1)] : List FactorBlock).map factorBlockValue).prod) = 411800824799859441492721457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_6655531
      · exact prime_thirtyOneAC_3867092129837756761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 411800824799859441492721457) ^ 205900412399929720746360728 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 411800824799859441492721457) ^ 61873474077404108176 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (3 : ZMod 411800824799859441492721457) ^ 106488496 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_872625557313987864115528801 : Nat.Prime 872625557313987864115528801 := by
  apply lucas_primality 872625557313987864115528801 (83 : ZMod 872625557313987864115528801)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 872625557313987864115528801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 872625557313987864115528801) ^ 436312778656993932057764400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 290875185771329288038509600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 174525111462797572823105760 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 124660793901998266302218400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 79329596119453442192320800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 67125042870306758778117600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 51330915136116933183266400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 45927660911262519163975200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 37940241622347298439805600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 30090536459103029797087200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 28149211526257673035984800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 23584474521999672003122400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 21283550178389947905256800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 20293617611953206142221600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 18566501219446550300330400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 16464633156867695549349600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 14790263683287929900263200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (83 : ZMod 872625557313987864115528801) ^ 14305337005147342034680800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2443351560479166019523480641 : Nat.Prime 2443351560479166019523480641 := by
  apply lucas_primality 2443351560479166019523480641 (67 : ZMod 2443351560479166019523480641)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2443351560479166019523480641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 2443351560479166019523480641) ^ 1221675780239583009761740320 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 814450520159722006507826880 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 488670312095833203904696128 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 349050222925595145646211520 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 222122869134469638138498240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 187950120036858924578729280 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 143726562381127412913145920 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 128597450551535053659130560 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 106232676542572435631455680 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 84253502085488483431844160 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 78817792273521484500757440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 66036528661599081608742720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 59593940499491854134719040 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 56822129313468977198220480 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 51986203414450340840925120 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 46100972839229547538178880 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 41412738313206203720736960 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (67 : ZMod 2443351560479166019523480641) ^ 40054943614412557697106240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_2617876671941963592346586401 : Nat.Prime 2617876671941963592346586401 := by
  apply lucas_primality 2617876671941963592346586401 (101 : ZMod 2617876671941963592346586401)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2617876671941963592346586401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 2617876671941963592346586401) ^ 1308938335970981796173293200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 872625557313987864115528800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 523575334388392718469317280 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 373982381705994798906655200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 237988788358360326576962400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 201375128610920276334352800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 153992745408350799549799200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 137782982733787557491925600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 113820724867041895319416800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 90271609377309089391261600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 84447634578773019107954400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 70753423565999016009367200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 63850650535169843715770400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 60880852835859618426664800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 55699503658339650900991200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 49393899470603086648048800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 44370791049863789700789600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (101 : ZMod 2617876671941963592346586401) ^ 42916011015442026104042400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3331843037017044572077473601 : Nat.Prime 3331843037017044572077473601 := by
  apply lucas_primality 3331843037017044572077473601 (107 : ZMod 3331843037017044572077473601)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3331843037017044572077473601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 3331843037017044572077473601) ^ 1665921518508522286038736800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 1110614345672348190692491200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 666368607403408914415494720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 475977576716720653153924800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 256295618232080351698267200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 195990766883355563063380800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 175360159843002345898814400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 144862740739871503133803200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 114891139207484295588878400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 107478807645711115228305600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 90049811811271474921012800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 81264464317488892001889600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 77484721791094059815755200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 70890277383341373873988800 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 62864962962585746642971200 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 56471915881644823255550400 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (107 : ZMod 3331843037017044572077473601) ^ 54620377656017124132417600 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem prime_thirtyOneAC_3665027340718749029285220961 : Nat.Prime 3665027340718749029285220961 := by
  apply lucas_primality 3665027340718749029285220961 (73 : ZMod 3665027340718749029285220961)
  · rw [← thirtyOneACFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3665027340718749029285220961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtyOneAC_2
      · exact prime_thirtyOneAC_3
      · exact prime_thirtyOneAC_5
      · exact prime_thirtyOneAC_7
      · exact prime_thirtyOneAC_11
      · exact prime_thirtyOneAC_13
      · exact prime_thirtyOneAC_17
      · exact prime_thirtyOneAC_19
      · exact prime_thirtyOneAC_23
      · exact prime_thirtyOneAC_29
      · exact prime_thirtyOneAC_31
      · exact prime_thirtyOneAC_37
      · exact prime_thirtyOneAC_41
      · exact prime_thirtyOneAC_43
      · exact prime_thirtyOneAC_47
      · exact prime_thirtyOneAC_53
      · exact prime_thirtyOneAC_59
      · exact prime_thirtyOneAC_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 3665027340718749029285220961) ^ 1832513670359374514642610480 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 1221675780239583009761740320 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 733005468143749805857044192 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 523575334388392718469317280 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 333184303701704457207747360 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 281925180055288386868093920 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 215589843571691119369718880 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 192896175827302580488695840 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 159349014813858653447183520 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 126380253128232725147766240 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 118226688410282226751136160 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 99054792992398622413114080 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 89390910749237781202078560 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 85233193970203465797330720 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 77979305121675511261387680 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 69151459258844321307268320 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 62119107469809305581105440 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide
    · change (73 : ZMod 3665027340718749029285220961) ^ 60082415421618836545659360 ≠ 1
      rw [← thirtyOneACFastPow_eq_pow]
      decide

private theorem phi_thirtyOneAC_36650273407187490292852209600 : Nat.totient 36650273407187490292852209600 = 4822712422240179820953600000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_5, prime_thirtyOneAC_7, prime_thirtyOneAC_11, prime_thirtyOneAC_13, prime_thirtyOneAC_17, prime_thirtyOneAC_19, prime_thirtyOneAC_23, prime_thirtyOneAC_29, prime_thirtyOneAC_31, prime_thirtyOneAC_37, prime_thirtyOneAC_41, prime_thirtyOneAC_43, prime_thirtyOneAC_47, prime_thirtyOneAC_53, prime_thirtyOneAC_59, prime_thirtyOneAC_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209601 : Nat.totient 36650273407187490292852209601 = 36537908506323084835741778112 := by
  rw [← show ((([(433, 1), (1319, 1), (64171845153858056601863, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_433, prime_thirtyOneAC_1319, prime_thirtyOneAC_64171845153858056601863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209602 : Nat.totient 36650273407187490292852209602 = 18300006010356128829850659840 := by
  rw [← show ((([(2, 1), (1481, 1), (1579, 1), (18329, 1), (113647, 1), (3761952324973, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_1481, prime_thirtyOneAC_1579, prime_thirtyOneAC_18329, prime_thirtyOneAC_113647, prime_thirtyOneAC_3761952324973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209603 : Nat.totient 36650273407187490292852209603 = 24424040113419561510278589440 := by
  rw [← show ((([(3, 1), (2579, 1), (22857113, 1), (62880611, 1), (3295842833, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_2579, prime_thirtyOneAC_22857113, prime_thirtyOneAC_62880611, prime_thirtyOneAC_3295842833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209604 : Nat.totient 36650273407187490292852209604 = 18046172153632536007430547456 := by
  rw [← show ((([(2, 2), (73, 1), (647, 1), (622448929, 1), (311663800781999, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_73, prime_thirtyOneAC_647, prime_thirtyOneAC_622448929, prime_thirtyOneAC_311663800781999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209605 : Nat.totient 36650273407187490292852209605 = 29320218725347715564476796688 := by
  rw [← show ((([(5, 1), (72885757927, 1), (100569094565484823, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_5, prime_thirtyOneAC_72885757927, prime_thirtyOneAC_100569094565484823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209606 : Nat.totient 36650273407187490292852209606 = 12216681251111801125625610240 := by
  rw [← show ((([(2, 1), (3, 1), (298049, 1), (366517, 1), (5480617, 1), (10202690741, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_298049, prime_thirtyOneAC_366517, prime_thirtyOneAC_5480617, prime_thirtyOneAC_10202690741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209607 : Nat.totient 36650273407187490292852209607 = 31101047060747875249820371200 := by
  rw [← show ((([(7, 1), (101, 1), (12757, 1), (4063584072952319855993, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_7, prime_thirtyOneAC_101, prime_thirtyOneAC_12757, prime_thirtyOneAC_4063584072952319855993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209608 : Nat.totient 36650273407187490292852209608 = 18323867386096786377627375168 := by
  rw [← show ((([(2, 3), (14437, 1), (317329374239692199667973, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_14437, prime_thirtyOneAC_317329374239692199667973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209609 : Nat.totient 36650273407187490292852209609 = 24209354910564769626022416480 := by
  rw [← show ((([(3, 2), (109, 1), (40020569471, 1), (933522838317659, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_109, prime_thirtyOneAC_40020569471, prime_thirtyOneAC_933522838317659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209610 : Nat.totient 36650273407187490292852209610 = 14660109362874996117140883840 := by
  rw [← show ((([(2, 1), (5, 1), (3665027340718749029285220961, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_5, prime_thirtyOneAC_3665027340718749029285220961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209611 : Nat.totient 36650273407187490292852209611 = 33318430370170445720774736000 := by
  rw [← show ((([(11, 1), (3331843037017044572077473601, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_11, prime_thirtyOneAC_3331843037017044572077473601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209612 : Nat.totient 36650273407187490292852209612 = 12063160402284812437583011584 := by
  rw [← show ((([(2, 2), (3, 1), (107, 1), (307, 1), (16659257077, 1), (5581079251037, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_107, prime_thirtyOneAC_307, prime_thirtyOneAC_16659257077, prime_thirtyOneAC_5581079251037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209613 : Nat.totient 36650273407187490292852209613 = 33755478651839021336805496320 := by
  rw [← show ((([(13, 1), (557, 1), (2281, 1), (2218979990470716935453, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_13, prime_thirtyOneAC_557, prime_thirtyOneAC_2281, prime_thirtyOneAC_2218979990470716935453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209614 : Nat.totient 36650273407187490292852209614 = 15707260031651781554079518400 := by
  rw [← show ((([(2, 1), (7, 1), (2617876671941963592346586401, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_7, prime_thirtyOneAC_2617876671941963592346586401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209615 : Nat.totient 36650273407187490292852209615 = 19546812483833328156187845120 := by
  rw [← show ((([(3, 1), (5, 1), (2443351560479166019523480641, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_5, prime_thirtyOneAC_2443351560479166019523480641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209616 : Nat.totient 36650273407187490292852209616 = 18323289831741630422564655360 := by
  rw [← show ((([(2, 4), (9931, 1), (11269039, 1), (20468092563622489, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_9931, prime_thirtyOneAC_11269039, prime_thirtyOneAC_20468092563622489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209617 : Nat.totient 36650273407187490292852209617 = 34494374970844159886919720000 := by
  rw [← show ((([(17, 1), (55066036951, 1), (39151145698669351, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_17, prime_thirtyOneAC_55066036951, prime_thirtyOneAC_39151145698669351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209618 : Nat.totient 36650273407187490292852209618 = 12214736164500348411352661112 := by
  rw [← show ((([(2, 1), (3, 2), (6043, 1), (336939649246947710784307, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_6043, prime_thirtyOneAC_336939649246947710784307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209619 : Nat.totient 36650273407187490292852209619 = 34454511828018275208263250048 := by
  rw [← show ((([(19, 2), (139, 1), (2027, 1), (952534507, 1), (378286419449, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_19, prime_thirtyOneAC_139, prime_thirtyOneAC_2027, prime_thirtyOneAC_952534507, prime_thirtyOneAC_378286419449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209620 : Nat.totient 36650273407187490292852209620 = 14659640351181359039342841984 := by
  rw [← show ((([(2, 2), (5, 1), (31469, 1), (4649527, 1), (12524358967375187, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_5, prime_thirtyOneAC_31469, prime_thirtyOneAC_4649527, prime_thirtyOneAC_12524358967375187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209621 : Nat.totient 36650273407187490292852209621 = 20817921152777066425635360768 := by
  rw [← show ((([(3, 1), (7, 1), (313, 1), (367, 1), (16033, 1), (947616752192632807, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_7, prime_thirtyOneAC_313, prime_thirtyOneAC_367, prime_thirtyOneAC_16033, prime_thirtyOneAC_947616752192632807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209622 : Nat.totient 36650273407187490292852209622 = 16612514354198010820110336000 := by
  rw [← show ((([(2, 1), (11, 1), (449, 1), (1741, 1), (332921, 1), (36356323, 1), (176071183, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_11, prime_thirtyOneAC_449, prime_thirtyOneAC_1741, prime_thirtyOneAC_332921, prime_thirtyOneAC_36356323, prime_thirtyOneAC_176071183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209623 : Nat.totient 36650273407187490292852209623 = 35033398997911286748000234240 := by
  rw [← show ((([(23, 1), (1607, 1), (26783, 1), (136463, 1), (12902831, 1), (21026857, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_23, prime_thirtyOneAC_1607, prime_thirtyOneAC_26783, prime_thirtyOneAC_136463, prime_thirtyOneAC_12902831, prime_thirtyOneAC_21026857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209624 : Nat.totient 36650273407187490292852209624 = 12216757802376229008099360800 := by
  rw [← show ((([(2, 3), (3, 1), (623427952331, 1), (2449512761802971, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_623427952331, prime_thirtyOneAC_2449512761802971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209625 : Nat.totient 36650273407187490292852209625 = 29311670081071792218275328000 := by
  rw [← show ((([(5, 3), (6053, 1), (10453, 1), (32561, 1), (142317349585973, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_5, prime_thirtyOneAC_6053, prime_thirtyOneAC_10453, prime_thirtyOneAC_32561, prime_thirtyOneAC_142317349585973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209626 : Nat.totient 36650273407187490292852209626 = 16893767292758778294835200000 := by
  rw [← show ((([(2, 1), (13, 1), (821, 1), (19301, 1), (63841, 1), (1393417375684441, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_13, prime_thirtyOneAC_821, prime_thirtyOneAC_19301, prime_thirtyOneAC_63841, prime_thirtyOneAC_1393417375684441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209627 : Nat.totient 36650273407187490292852209627 = 24269270494391231040690912000 := by
  rw [← show ((([(3, 3), (151, 1), (9973, 1), (3388799731, 1), (265989678377, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_151, prime_thirtyOneAC_9973, prime_thirtyOneAC_3388799731, prime_thirtyOneAC_265989678377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209628 : Nat.totient 36650273407187490292852209628 = 15684262579189626676255089264 := by
  rw [← show ((([(2, 2), (7, 1), (683, 1), (1916454371846239818701747, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_7, prime_thirtyOneAC_683, prime_thirtyOneAC_1916454371846239818701747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209629 : Nat.totient 36650273407187490292852209629 = 35274807389602710730722781440 := by
  rw [← show ((([(29, 1), (317, 1), (1049827, 1), (55159861, 1), (68846054699, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_29, prime_thirtyOneAC_317, prime_thirtyOneAC_1049827, prime_thirtyOneAC_55159861, prime_thirtyOneAC_68846054699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209630 : Nat.totient 36650273407187490292852209630 = 9773357136705396471170309376 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (212873, 1), (3060583, 1), (1875129307657919, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_5, prime_thirtyOneAC_212873, prime_thirtyOneAC_3060583, prime_thirtyOneAC_1875129307657919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209631 : Nat.totient 36650273407187490292852209631 = 35116644835598869185029285760 := by
  rw [← show ((([(31, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_31, prime_thirtyOneAC_103, prime_thirtyOneAC_5009, prime_thirtyOneAC_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209632 : Nat.totient 36650273407187490292852209632 = 18325136689680860373026904192 := by
  rw [← show ((([(2, 5), (1317134227, 1), (869555297020315813, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_1317134227, prime_thirtyOneAC_869555297020315813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209633 : Nat.totient 36650273407187490292852209633 = 21944668998827120876333559440 := by
  rw [← show ((([(3, 1), (11, 1), (83, 1), (13380895730992146875813147, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_11, prime_thirtyOneAC_83, prime_thirtyOneAC_13380895730992146875813147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209634 : Nat.totient 36650273407187490292852209634 = 17159638258773117798432618240 := by
  rw [← show ((([(2, 1), (17, 1), (197, 1), (330579971, 1), (16552192875913423, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_17, prime_thirtyOneAC_197, prime_thirtyOneAC_330579971, prime_thirtyOneAC_16552192875913423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209635 : Nat.totient 36650273407187490292852209635 = 25117293951872434260752049792 := by
  rw [← show ((([(5, 1), (7, 1), (2309, 1), (7307, 1), (62064910601561039047, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_5, prime_thirtyOneAC_7, prime_thirtyOneAC_2309, prime_thirtyOneAC_7307, prime_thirtyOneAC_62064910601561039047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209636 : Nat.totient 36650273407187490292852209636 = 12175062006292439464791570240 := by
  rw [← show ((([(2, 2), (3, 2), (293, 1), (32296087, 1), (107586354348967211, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_293, prime_thirtyOneAC_32296087, prime_thirtyOneAC_107586354348967211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209637 : Nat.totient 36650273407187490292852209637 = 35208336534106347164453127552 := by
  rw [← show ((([(37, 1), (79, 1), (2694816743, 1), (4652851227829433, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_37, prime_thirtyOneAC_79, prime_thirtyOneAC_2694816743, prime_thirtyOneAC_4652851227829433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209638 : Nat.totient 36650273407187490292852209638 = 17291489864997243270899025000 := by
  rw [← show ((([(2, 1), (19, 1), (251, 1), (3842553303332720726866451, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_19, prime_thirtyOneAC_251, prime_thirtyOneAC_3842553303332720726866451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209639 : Nat.totient 36650273407187490292852209639 = 22093267841504397357967648512 := by
  rw [← show ((([(3, 1), (13, 1), (67, 1), (179, 1), (78358258999774420319657, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_13, prime_thirtyOneAC_67, prime_thirtyOneAC_179, prime_thirtyOneAC_78358258999774420319657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209640 : Nat.totient 36650273407187490292852209640 = 14653064620269097512567500800 := by
  rw [← show ((([(2, 3), (5, 1), (2081, 1), (440296412868662785834361, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_5, prime_thirtyOneAC_2081, prime_thirtyOneAC_440296412868662785834361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209641 : Nat.totient 36650273407187490292852209641 = 35749619517144409324449214080 := by
  rw [← show ((([(41, 1), (5323, 1), (1302383, 1), (128943120786088589, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_41, prime_thirtyOneAC_5323, prime_thirtyOneAC_1302383, prime_thirtyOneAC_128943120786088589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209642 : Nat.totient 36650273407187490292852209642 = 10471506687767854369386345600 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (872625557313987864115528801, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_7, prime_thirtyOneAC_872625557313987864115528801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209643 : Nat.totient 36650273407187490292852209643 = 35787783593736092973648494880 := by
  rw [← show ((([(43, 1), (4547, 1), (16267, 1), (421831, 1), (27317304886679, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_43, prime_thirtyOneAC_4547, prime_thirtyOneAC_16267, prime_thirtyOneAC_421831, prime_thirtyOneAC_27317304886679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209644 : Nat.totient 36650273407187490292852209644 = 16655953145761244419317725760 := by
  rw [← show ((([(2, 2), (11, 1), (5107, 1), (4331009479, 1), (37659066478717, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_11, prime_thirtyOneAC_5107, prime_thirtyOneAC_4331009479, prime_thirtyOneAC_37659066478717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209645 : Nat.totient 36650273407187490292852209645 = 19543243593476593935235333248 := by
  rw [← show ((([(3, 2), (5, 1), (5477, 1), (148703764863925873015853, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_5, prime_thirtyOneAC_5477, prime_thirtyOneAC_148703764863925873015853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209646 : Nat.totient 36650273407187490292852209646 = 17514710579210766142708748800 := by
  rw [← show ((([(2, 1), (23, 1), (1283, 1), (945809, 1), (35343701, 1), (18577071983, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_23, prime_thirtyOneAC_1283, prime_thirtyOneAC_945809, prime_thirtyOneAC_35343701, prime_thirtyOneAC_18577071983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209647 : Nat.totient 36650273407187490292852209647 = 35867073529077775665072093184 := by
  rw [← show ((([(47, 1), (10529, 1), (74061454194772068820769, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_47, prime_thirtyOneAC_10529, prime_thirtyOneAC_74061454194772068820769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209648 : Nat.totient 36650273407187490292852209648 = 12215903662858502555835896512 := by
  rw [← show ((([(2, 4), (3, 1), (14303, 1), (53383721082971361329867, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_14303, prime_thirtyOneAC_53383721082971361329867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209649 : Nat.totient 36650273407187490292852209649 = 31414123166837623323105708000 := by
  rw [← show ((([(7, 2), (90071, 1), (652811, 1), (12720632046923221, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_7, prime_thirtyOneAC_90071, prime_thirtyOneAC_652811, prime_thirtyOneAC_12720632046923221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209650 : Nat.totient 36650273407187490292852209650 = 14642022409903965579607497600 := by
  rw [← show ((([(2, 1), (5, 2), (811, 1), (1412057, 1), (640079815404794459, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_5, prime_thirtyOneAC_811, prime_thirtyOneAC_1412057, prime_thirtyOneAC_640079815404794459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209651 : Nat.totient 36650273407187490292852209651 = 22996249469320868388176025728 := by
  rw [← show ((([(3, 1), (17, 1), (44944439, 1), (15989359927390284359, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_17, prime_thirtyOneAC_44944439, prime_thirtyOneAC_15989359927390284359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209652 : Nat.totient 36650273407187490292852209652 = 16913419584865178205218250240 := by
  rw [← show ((([(2, 2), (13, 1), (22093, 1), (25031, 1), (26029, 1), (48964745208143, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_13, prime_thirtyOneAC_22093, prime_thirtyOneAC_25031, prime_thirtyOneAC_26029, prime_thirtyOneAC_48964745208143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209653 : Nat.totient 36650273407187490292852209653 = 35949882300450787626044490000 := by
  rw [← show ((([(53, 1), (4051, 1), (170702195158835648746651, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_53, prime_thirtyOneAC_4051, prime_thirtyOneAC_170702195158835648746651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209654 : Nat.totient 36650273407187490292852209654 = 12044690791094480377932647280 := by
  rw [← show ((([(2, 1), (3, 4), (71, 1), (3186426135210179994162077, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_71, prime_thirtyOneAC_3186426135210179994162077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209655 : Nat.totient 36650273407187490292852209655 = 26654744295047673515491260480 := by
  rw [← show ((([(5, 1), (11, 2), (24483717077, 1), (2474255200665943, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_5, prime_thirtyOneAC_11, prime_thirtyOneAC_24483717077, prime_thirtyOneAC_2474255200665943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209656 : Nat.totient 36650273407187490292852209656 = 15657610725673738715901450240 := by
  rw [← show ((([(2, 3), (7, 1), (499, 1), (863, 1), (2076433, 1), (731913787141181, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_7, prime_thirtyOneAC_499, prime_thirtyOneAC_863, prime_thirtyOneAC_2076433, prime_thirtyOneAC_731913787141181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209657 : Nat.totient 36650273407187490292852209657 = 22923087046971902727583334400 := by
  rw [← show ((([(3, 1), (19, 1), (191, 1), (223, 1), (4120097, 1), (3664010351887681, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_19, prime_thirtyOneAC_191, prime_thirtyOneAC_223, prime_thirtyOneAC_4120097, prime_thirtyOneAC_3664010351887681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209658 : Nat.totient 36650273407187490292852209658 = 17656297576913014544652422512 := by
  rw [← show ((([(2, 1), (29, 1), (479, 1), (1319209322841677715529919, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_29, prime_thirtyOneAC_479, prime_thirtyOneAC_1319209322841677715529919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209659 : Nat.totient 36650273407187490292852209659 = 36026477001616100377131142656 := by
  rw [← show ((([(59, 1), (13829, 1), (13052550013, 1), (3441430984913, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_59, prime_thirtyOneAC_13829, prime_thirtyOneAC_13052550013, prime_thirtyOneAC_3441430984913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209660 : Nat.totient 36650273407187490292852209660 = 9773182332665660521562898432 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (43649, 1), (63479879993, 1), (220452776473, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_5, prime_thirtyOneAC_43649, prime_thirtyOneAC_63479879993, prime_thirtyOneAC_220452776473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209661 : Nat.totient 36650273407187490292852209661 = 35933534624549823914545675200 := by
  rw [← show ((([(61, 1), (311, 1), (60159925027, 1), (32112913419533, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_61, prime_thirtyOneAC_311, prime_thirtyOneAC_60159925027, prime_thirtyOneAC_32112913419533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209662 : Nat.totient 36650273407187490292852209662 = 17734003247037367361466183000 := by
  rw [← show ((([(2, 1), (31, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_31, prime_thirtyOneAC_1222615931, prime_thirtyOneAC_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209663 : Nat.totient 36650273407187490292852209663 = 20834500352864539263442255872 := by
  rw [← show ((([(3, 2), (7, 1), (193, 1), (3014250629754707648067457, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_7, prime_thirtyOneAC_193, prime_thirtyOneAC_3014250629754707648067457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209664 : Nat.totient 36650273407187490292852209664 = 18324682432507890261095219200 := by
  rw [← show ((([(2, 11), (40763, 1), (3884081, 1), (113029771412981, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_40763, prime_thirtyOneAC_3884081, prime_thirtyOneAC_113029771412981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209665 : Nat.totient 36650273407187490292852209665 = 26917445759595809744508779520 := by
  rw [← show ((([(5, 1), (13, 1), (347, 1), (389, 1), (365160181, 1), (11439350643067, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_5, prime_thirtyOneAC_13, prime_thirtyOneAC_347, prime_thirtyOneAC_389, prime_thirtyOneAC_365160181, prime_thirtyOneAC_11439350643067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209666 : Nat.totient 36650273407187490292852209666 = 11007856135991470338990489600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (113, 1), (5453879, 1), (12998593, 1), (69319112791, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_11, prime_thirtyOneAC_113, prime_thirtyOneAC_5453879, prime_thirtyOneAC_12998593, prime_thirtyOneAC_69319112791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209667 : Nat.totient 36650273407187490292852209667 = 36650270233954467271315885320 := by
  rw [← show ((([(11549821, 1), (3173233023021524774527, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_11549821, prime_thirtyOneAC_3173233023021524774527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209668 : Nat.totient 36650273407187490292852209668 = 17246199826558348985463860736 := by
  rw [← show ((([(2, 2), (17, 1), (20959, 1), (104677, 1), (245666806856293507, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_17, prime_thirtyOneAC_20959, prime_thirtyOneAC_104677, prime_thirtyOneAC_245666806856293507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209669 : Nat.totient 36650273407187490292852209669 = 23371188824056382736802092608 := by
  rw [← show ((([(3, 1), (23, 1), (1526575517, 1), (347944387157928053, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_23, prime_thirtyOneAC_1526575517, prime_thirtyOneAC_347944387157928053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209670 : Nat.totient 36650273407187490292852209670 = 12565434565339099287746913888 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (33647, 1), (15560832596914813162223, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_5, prime_thirtyOneAC_7, prime_thirtyOneAC_33647, prime_thirtyOneAC_15560832596914813162223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209671 : Nat.totient 36650273407187490292852209671 = 36404298019746998905016912032 := by
  rw [← show ((([(149, 1), (91438103, 1), (2690071001472801293, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_149, prime_thirtyOneAC_91438103, prime_thirtyOneAC_2690071001472801293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209672 : Nat.totient 36650273407187490292852209672 = 12002385142789926005178408960 := by
  rw [← show ((([(2, 3), (3, 2), (97, 1), (137, 1), (69539, 1), (550838110474311931, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_97, prime_thirtyOneAC_137, prime_thirtyOneAC_69539, prime_thirtyOneAC_550838110474311931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209673 : Nat.totient 36650273407187490292852209673 = 36238472582387630851359488128 := by
  rw [← show ((([(89, 1), (411800824799859441492721457, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_89, prime_thirtyOneAC_411800824799859441492721457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209674 : Nat.totient 36650273407187490292852209674 = 17829862561265928755849625600 := by
  rw [← show ((([(2, 1), (37, 1), (100525921, 1), (4926828424302554881, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_37, prime_thirtyOneAC_100525921, prime_thirtyOneAC_4926828424302554881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209675 : Nat.totient 36650273407187490292852209675 = 19473040961757383222559744000 := by
  rw [← show ((([(3, 1), (5, 2), (271, 1), (11863, 1), (13613513, 1), (11165596354721, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_5, prime_thirtyOneAC_271, prime_thirtyOneAC_11863, prime_thirtyOneAC_13613513, prime_thirtyOneAC_11165596354721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209676 : Nat.totient 36650273407187490292852209676 = 17360140870112485195891832832 := by
  rw [← show ((([(2, 2), (19, 1), (33713, 1), (14304287354084669154977, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_19, prime_thirtyOneAC_33713, prime_thirtyOneAC_14304287354084669154977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209677 : Nat.totient 36650273407187490292852209677 = 28167440156386756460615819520 := by
  rw [← show ((([(7, 1), (11, 1), (73, 1), (6520240776941378810327737, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_7, prime_thirtyOneAC_11, prime_thirtyOneAC_73, prime_thirtyOneAC_6520240776941378810327737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209678 : Nat.totient 36650273407187490292852209678 = 11214675119145877802854963200 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (181, 1), (461093, 1), (2909981, 1), (1934752242637, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_13, prime_thirtyOneAC_181, prime_thirtyOneAC_461093, prime_thirtyOneAC_2909981, prime_thirtyOneAC_1934752242637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209679 : Nat.totient 36650273407187490292852209679 = 36492426925874144520305944320 := by
  rw [← show ((([(277, 1), (1433, 1), (709271, 1), (130178437986031789, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_277, prime_thirtyOneAC_1433, prime_thirtyOneAC_709271, prime_thirtyOneAC_130178437986031789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209680 : Nat.totient 36650273407187490292852209680 = 14660103768715225376743557120 := by
  rw [← show ((([(2, 4), (5, 1), (2684273, 1), (110502167, 1), (1544506548331, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_5, prime_thirtyOneAC_2684273, prime_thirtyOneAC_110502167, prime_thirtyOneAC_1544506548331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209681 : Nat.totient 36650273407187490292852209681 = 24431867697673412211351710160 := by
  rw [← show ((([(3, 3), (14827, 1), (133760968291, 1), (684432719779, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_14827, prime_thirtyOneAC_133760968291, prime_thirtyOneAC_684432719779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209682 : Nat.totient 36650273407187490292852209682 = 17860149010260074904768460800 := by
  rw [← show ((([(2, 1), (41, 1), (1069, 1), (13687, 1), (4540337, 1), (6728051467091, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_41, prime_thirtyOneAC_1069, prime_thirtyOneAC_13687, prime_thirtyOneAC_4540337, prime_thirtyOneAC_6728051467091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209683 : Nat.totient 36650273407187490292852209683 = 36650236113784823939031452544 := by
  rw [← show ((([(1053713, 1), (14593687, 1), (2383361135673493, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_1053713, prime_thirtyOneAC_14593687, prime_thirtyOneAC_2383361135673493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209684 : Nat.totient 36650273407187490292852209684 = 10452124079008790785785953280 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (661, 1), (2953, 1), (223528563048523659397, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_7, prime_thirtyOneAC_661, prime_thirtyOneAC_2953, prime_thirtyOneAC_223528563048523659397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209685 : Nat.totient 36650273407187490292852209685 = 27595499466626721207943168000 := by
  rw [← show ((([(5, 1), (17, 1), (54050561, 1), (7977339719811275201, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_5, prime_thirtyOneAC_17, prime_thirtyOneAC_54050561, prime_thirtyOneAC_7977339719811275201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209686 : Nat.totient 36650273407187490292852209686 = 17883947551360011999576056064 := by
  rw [← show ((([(2, 1), (43, 1), (1193, 1), (900773, 1), (396572836680015109, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_43, prime_thirtyOneAC_1193, prime_thirtyOneAC_900773, prime_thirtyOneAC_396572836680015109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209687 : Nat.totient 36650273407187490292852209687 = 23590980558283234414526258400 := by
  rw [← show ((([(3, 1), (29, 1), (919599391, 1), (458098944551652511, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_29, prime_thirtyOneAC_919599391, prime_thirtyOneAC_458098944551652511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209688 : Nat.totient 36650273407187490292852209688 = 16655035381116691557382963200 := by
  rw [← show ((([(2, 3), (11, 1), (4861, 1), (22129, 1), (1181738057, 1), (3276316997, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_11, prime_thirtyOneAC_4861, prime_thirtyOneAC_22129, prime_thirtyOneAC_1181738057, prime_thirtyOneAC_3276316997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209689 : Nat.totient 36650273407187490292852209689 = 36552922461885465867323828736 := by
  rw [← show ((([(673, 1), (859, 1), (126013, 1), (503099215085633879, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_673, prime_thirtyOneAC_859, prime_thirtyOneAC_126013, prime_thirtyOneAC_503099215085633879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209690 : Nat.totient 36650273407187490292852209690 = 9761731561078903552654789632 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1237, 1), (4409, 1), (6263, 1), (11921818319404579, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_5, prime_thirtyOneAC_1237, prime_thirtyOneAC_4409, prime_thirtyOneAC_6263, prime_thirtyOneAC_11921818319404579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209691 : Nat.totient 36650273407187490292852209691 = 28959257409928494451845995520 := by
  rw [← show ((([(7, 1), (13, 1), (853, 1), (6089, 1), (3217931, 1), (24097061922463, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_7, prime_thirtyOneAC_13, prime_thirtyOneAC_853, prime_thirtyOneAC_6089, prime_thirtyOneAC_3217931, prime_thirtyOneAC_24097061922463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209692 : Nat.totient 36650273407187490292852209692 = 17528391629524451879190187200 := by
  rw [← show ((([(2, 2), (23, 1), (398372537034646633617958801, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_23, prime_thirtyOneAC_398372537034646633617958801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209693 : Nat.totient 36650273407187490292852209693 = 23645337682056445350227232000 := by
  rw [← show ((([(3, 1), (31, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_31, prime_thirtyOneAC_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209694 : Nat.totient 36650273407187490292852209694 = 17935240098815103836312519584 := by
  rw [← show ((([(2, 1), (47, 1), (226540109, 1), (1721092690073604389, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_47, prime_thirtyOneAC_226540109, prime_thirtyOneAC_1721092690073604389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209695 : Nat.totient 36650273407187490292852209695 = 27769399346859709411470708000 := by
  rw [← show ((([(5, 1), (19, 1), (3631, 1), (106249614886974706961551, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_5, prime_thirtyOneAC_19, prime_thirtyOneAC_3631, prime_thirtyOneAC_106249614886974706961551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209696 : Nat.totient 36650273407187490292852209696 = 12120556091129186381045519616 := by
  rw [← show ((([(2, 5), (3, 1), (127, 1), (1790879, 1), (1678556719318268747, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_3, prime_thirtyOneAC_127, prime_thirtyOneAC_1790879, prime_thirtyOneAC_1678556719318268747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209697 : Nat.totient 36650273407187490292852209697 = 36646759141761961141508617344 := by
  rw [← show ((([(10429, 1), (586272326317, 1), (5994254204329, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_10429, prime_thirtyOneAC_586272326317, prime_thirtyOneAC_5994254204329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209698 : Nat.totient 36650273407187490292852209698 = 15707260031651781554079518400 := by
  rw [← show ((([(2, 1), (7, 2), (373982381705994798906655201, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_2, prime_thirtyOneAC_7, prime_thirtyOneAC_373982381705994798906655201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyOneAC_36650273407187490292852209699 : Nat.totient 36650273407187490292852209699 = 22212010066178215954936408320 := by
  rw [← show ((([(3, 2), (11, 1), (80233, 1), (4614121145797648476697, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187490292852209699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyOneAC_3, prime_thirtyOneAC_11, prime_thirtyOneAC_80233, prime_thirtyOneAC_4614121145797648476697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyOneAC : certifiedKill 1 36650273407187490292852209599 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyOneAC_36650273407187490292852209600, phi_thirtyOneAC_36650273407187490292852209601, phi_thirtyOneAC_36650273407187490292852209602,
    phi_thirtyOneAC_36650273407187490292852209603, phi_thirtyOneAC_36650273407187490292852209604, phi_thirtyOneAC_36650273407187490292852209605,
    phi_thirtyOneAC_36650273407187490292852209606, phi_thirtyOneAC_36650273407187490292852209607, phi_thirtyOneAC_36650273407187490292852209608,
    phi_thirtyOneAC_36650273407187490292852209609, phi_thirtyOneAC_36650273407187490292852209610, phi_thirtyOneAC_36650273407187490292852209611,
    phi_thirtyOneAC_36650273407187490292852209612, phi_thirtyOneAC_36650273407187490292852209613, phi_thirtyOneAC_36650273407187490292852209614,
    phi_thirtyOneAC_36650273407187490292852209615, phi_thirtyOneAC_36650273407187490292852209616, phi_thirtyOneAC_36650273407187490292852209617,
    phi_thirtyOneAC_36650273407187490292852209618, phi_thirtyOneAC_36650273407187490292852209619, phi_thirtyOneAC_36650273407187490292852209620,
    phi_thirtyOneAC_36650273407187490292852209621, phi_thirtyOneAC_36650273407187490292852209622, phi_thirtyOneAC_36650273407187490292852209623,
    phi_thirtyOneAC_36650273407187490292852209624, phi_thirtyOneAC_36650273407187490292852209625, phi_thirtyOneAC_36650273407187490292852209626,
    phi_thirtyOneAC_36650273407187490292852209627, phi_thirtyOneAC_36650273407187490292852209628, phi_thirtyOneAC_36650273407187490292852209629,
    phi_thirtyOneAC_36650273407187490292852209630, phi_thirtyOneAC_36650273407187490292852209631, phi_thirtyOneAC_36650273407187490292852209632,
    phi_thirtyOneAC_36650273407187490292852209633, phi_thirtyOneAC_36650273407187490292852209634, phi_thirtyOneAC_36650273407187490292852209635,
    phi_thirtyOneAC_36650273407187490292852209636, phi_thirtyOneAC_36650273407187490292852209637, phi_thirtyOneAC_36650273407187490292852209638,
    phi_thirtyOneAC_36650273407187490292852209639, phi_thirtyOneAC_36650273407187490292852209640, phi_thirtyOneAC_36650273407187490292852209641,
    phi_thirtyOneAC_36650273407187490292852209642, phi_thirtyOneAC_36650273407187490292852209643, phi_thirtyOneAC_36650273407187490292852209644,
    phi_thirtyOneAC_36650273407187490292852209645, phi_thirtyOneAC_36650273407187490292852209646, phi_thirtyOneAC_36650273407187490292852209647,
    phi_thirtyOneAC_36650273407187490292852209648, phi_thirtyOneAC_36650273407187490292852209649, phi_thirtyOneAC_36650273407187490292852209650,
    phi_thirtyOneAC_36650273407187490292852209651, phi_thirtyOneAC_36650273407187490292852209652, phi_thirtyOneAC_36650273407187490292852209653,
    phi_thirtyOneAC_36650273407187490292852209654, phi_thirtyOneAC_36650273407187490292852209655, phi_thirtyOneAC_36650273407187490292852209656,
    phi_thirtyOneAC_36650273407187490292852209657, phi_thirtyOneAC_36650273407187490292852209658, phi_thirtyOneAC_36650273407187490292852209659,
    phi_thirtyOneAC_36650273407187490292852209660, phi_thirtyOneAC_36650273407187490292852209661, phi_thirtyOneAC_36650273407187490292852209662,
    phi_thirtyOneAC_36650273407187490292852209663, phi_thirtyOneAC_36650273407187490292852209664, phi_thirtyOneAC_36650273407187490292852209665,
    phi_thirtyOneAC_36650273407187490292852209666, phi_thirtyOneAC_36650273407187490292852209667, phi_thirtyOneAC_36650273407187490292852209668,
    phi_thirtyOneAC_36650273407187490292852209669, phi_thirtyOneAC_36650273407187490292852209670, phi_thirtyOneAC_36650273407187490292852209671,
    phi_thirtyOneAC_36650273407187490292852209672, phi_thirtyOneAC_36650273407187490292852209673, phi_thirtyOneAC_36650273407187490292852209674,
    phi_thirtyOneAC_36650273407187490292852209675, phi_thirtyOneAC_36650273407187490292852209676, phi_thirtyOneAC_36650273407187490292852209677,
    phi_thirtyOneAC_36650273407187490292852209678, phi_thirtyOneAC_36650273407187490292852209679, phi_thirtyOneAC_36650273407187490292852209680,
    phi_thirtyOneAC_36650273407187490292852209681, phi_thirtyOneAC_36650273407187490292852209682, phi_thirtyOneAC_36650273407187490292852209683,
    phi_thirtyOneAC_36650273407187490292852209684, phi_thirtyOneAC_36650273407187490292852209685, phi_thirtyOneAC_36650273407187490292852209686,
    phi_thirtyOneAC_36650273407187490292852209687, phi_thirtyOneAC_36650273407187490292852209688, phi_thirtyOneAC_36650273407187490292852209689,
    phi_thirtyOneAC_36650273407187490292852209690, phi_thirtyOneAC_36650273407187490292852209691, phi_thirtyOneAC_36650273407187490292852209692,
    phi_thirtyOneAC_36650273407187490292852209693, phi_thirtyOneAC_36650273407187490292852209694, phi_thirtyOneAC_36650273407187490292852209695,
    phi_thirtyOneAC_36650273407187490292852209696, phi_thirtyOneAC_36650273407187490292852209697, phi_thirtyOneAC_36650273407187490292852209698,
    phi_thirtyOneAC_36650273407187490292852209699]

end TotientTailPeriodKiller
end Erdos249257
