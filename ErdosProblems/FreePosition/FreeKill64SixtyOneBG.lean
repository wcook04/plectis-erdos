import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 61P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyOneBGFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyOneBGFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixtyOneBGFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyOneBGFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyOneBGFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyOneBGFastPow a n * sixtyOneBGFastPow a n * a
        else sixtyOneBGFastPow a n * sixtyOneBGFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyOneBG_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtyOneBG_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtyOneBG_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtyOneBG_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtyOneBG_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtyOneBG_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtyOneBG_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtyOneBG_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtyOneBG_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtyOneBG_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtyOneBG_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtyOneBG_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtyOneBG_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtyOneBG_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtyOneBG_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtyOneBG_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtyOneBG_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtyOneBG_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtyOneBG_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtyOneBG_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtyOneBG_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtyOneBG_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtyOneBG_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtyOneBG_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtyOneBG_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtyOneBG_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtyOneBG_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtyOneBG_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtyOneBG_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtyOneBG_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtyOneBG_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtyOneBG_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtyOneBG_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtyOneBG_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixtyOneBG_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtyOneBG_151 : Nat.Prime 151 := by norm_num
private theorem prime_sixtyOneBG_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixtyOneBG_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtyOneBG_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixtyOneBG_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtyOneBG_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtyOneBG_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixtyOneBG_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixtyOneBG_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixtyOneBG_197 : Nat.Prime 197 := by norm_num
private theorem prime_sixtyOneBG_199 : Nat.Prime 199 := by norm_num
private theorem prime_sixtyOneBG_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtyOneBG_223 : Nat.Prime 223 := by norm_num
private theorem prime_sixtyOneBG_229 : Nat.Prime 229 := by norm_num
private theorem prime_sixtyOneBG_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixtyOneBG_241 : Nat.Prime 241 := by norm_num
private theorem prime_sixtyOneBG_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtyOneBG_257 : Nat.Prime 257 := by norm_num
private theorem prime_sixtyOneBG_263 : Nat.Prime 263 := by norm_num
private theorem prime_sixtyOneBG_271 : Nat.Prime 271 := by norm_num
private theorem prime_sixtyOneBG_277 : Nat.Prime 277 := by norm_num
private theorem prime_sixtyOneBG_283 : Nat.Prime 283 := by norm_num
private theorem prime_sixtyOneBG_293 : Nat.Prime 293 := by norm_num
private theorem prime_sixtyOneBG_307 : Nat.Prime 307 := by norm_num
private theorem prime_sixtyOneBG_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtyOneBG_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtyOneBG_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtyOneBG_349 : Nat.Prime 349 := by norm_num
private theorem prime_sixtyOneBG_353 : Nat.Prime 353 := by norm_num
private theorem prime_sixtyOneBG_359 : Nat.Prime 359 := by norm_num
private theorem prime_sixtyOneBG_367 : Nat.Prime 367 := by norm_num
private theorem prime_sixtyOneBG_373 : Nat.Prime 373 := by norm_num
private theorem prime_sixtyOneBG_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtyOneBG_383 : Nat.Prime 383 := by norm_num
private theorem prime_sixtyOneBG_389 : Nat.Prime 389 := by norm_num
private theorem prime_sixtyOneBG_397 : Nat.Prime 397 := by norm_num
private theorem prime_sixtyOneBG_401 : Nat.Prime 401 := by norm_num
private theorem prime_sixtyOneBG_419 : Nat.Prime 419 := by norm_num
private theorem prime_sixtyOneBG_431 : Nat.Prime 431 := by norm_num
private theorem prime_sixtyOneBG_433 : Nat.Prime 433 := by norm_num
private theorem prime_sixtyOneBG_439 : Nat.Prime 439 := by norm_num
private theorem prime_sixtyOneBG_443 : Nat.Prime 443 := by norm_num
private theorem prime_sixtyOneBG_449 : Nat.Prime 449 := by norm_num
private theorem prime_sixtyOneBG_457 : Nat.Prime 457 := by norm_num
private theorem prime_sixtyOneBG_461 : Nat.Prime 461 := by norm_num
private theorem prime_sixtyOneBG_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixtyOneBG_503 : Nat.Prime 503 := by norm_num
private theorem prime_sixtyOneBG_509 : Nat.Prime 509 := by norm_num
private theorem prime_sixtyOneBG_541 : Nat.Prime 541 := by norm_num
private theorem prime_sixtyOneBG_557 : Nat.Prime 557 := by norm_num
private theorem prime_sixtyOneBG_571 : Nat.Prime 571 := by norm_num
private theorem prime_sixtyOneBG_577 : Nat.Prime 577 := by norm_num
private theorem prime_sixtyOneBG_593 : Nat.Prime 593 := by norm_num
private theorem prime_sixtyOneBG_599 : Nat.Prime 599 := by norm_num
private theorem prime_sixtyOneBG_601 : Nat.Prime 601 := by norm_num
private theorem prime_sixtyOneBG_607 : Nat.Prime 607 := by norm_num
private theorem prime_sixtyOneBG_613 : Nat.Prime 613 := by norm_num
private theorem prime_sixtyOneBG_617 : Nat.Prime 617 := by norm_num
private theorem prime_sixtyOneBG_647 : Nat.Prime 647 := by norm_num
private theorem prime_sixtyOneBG_653 : Nat.Prime 653 := by norm_num
private theorem prime_sixtyOneBG_659 : Nat.Prime 659 := by norm_num
private theorem prime_sixtyOneBG_661 : Nat.Prime 661 := by norm_num
private theorem prime_sixtyOneBG_683 : Nat.Prime 683 := by norm_num
private theorem prime_sixtyOneBG_743 : Nat.Prime 743 := by norm_num
private theorem prime_sixtyOneBG_751 : Nat.Prime 751 := by norm_num
private theorem prime_sixtyOneBG_757 : Nat.Prime 757 := by norm_num
private theorem prime_sixtyOneBG_761 : Nat.Prime 761 := by norm_num
private theorem prime_sixtyOneBG_769 : Nat.Prime 769 := by norm_num
private theorem prime_sixtyOneBG_787 : Nat.Prime 787 := by norm_num
private theorem prime_sixtyOneBG_809 : Nat.Prime 809 := by norm_num
private theorem prime_sixtyOneBG_811 : Nat.Prime 811 := by norm_num
private theorem prime_sixtyOneBG_829 : Nat.Prime 829 := by norm_num
private theorem prime_sixtyOneBG_853 : Nat.Prime 853 := by norm_num
private theorem prime_sixtyOneBG_857 : Nat.Prime 857 := by norm_num
private theorem prime_sixtyOneBG_863 : Nat.Prime 863 := by norm_num
private theorem prime_sixtyOneBG_877 : Nat.Prime 877 := by norm_num
private theorem prime_sixtyOneBG_883 : Nat.Prime 883 := by norm_num
private theorem prime_sixtyOneBG_919 : Nat.Prime 919 := by norm_num
private theorem prime_sixtyOneBG_941 : Nat.Prime 941 := by norm_num
private theorem prime_sixtyOneBG_967 : Nat.Prime 967 := by norm_num
private theorem prime_sixtyOneBG_971 : Nat.Prime 971 := by norm_num
private theorem prime_sixtyOneBG_991 : Nat.Prime 991 := by norm_num
private theorem prime_sixtyOneBG_997 : Nat.Prime 997 := by norm_num
private theorem prime_sixtyOneBG_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_sixtyOneBG_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_sixtyOneBG_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_sixtyOneBG_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_sixtyOneBG_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_sixtyOneBG_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_sixtyOneBG_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_sixtyOneBG_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_sixtyOneBG_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_sixtyOneBG_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_sixtyOneBG_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_sixtyOneBG_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_sixtyOneBG_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_sixtyOneBG_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_sixtyOneBG_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_sixtyOneBG_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_sixtyOneBG_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_sixtyOneBG_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_sixtyOneBG_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_sixtyOneBG_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_sixtyOneBG_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_sixtyOneBG_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_sixtyOneBG_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_sixtyOneBG_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_sixtyOneBG_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_sixtyOneBG_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_sixtyOneBG_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_sixtyOneBG_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_sixtyOneBG_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_sixtyOneBG_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_sixtyOneBG_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_sixtyOneBG_2411 : Nat.Prime 2411 := by norm_num
private theorem prime_sixtyOneBG_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_sixtyOneBG_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_sixtyOneBG_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_sixtyOneBG_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_sixtyOneBG_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_sixtyOneBG_2909 : Nat.Prime 2909 := by norm_num
private theorem prime_sixtyOneBG_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_sixtyOneBG_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_sixtyOneBG_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_sixtyOneBG_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_sixtyOneBG_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_sixtyOneBG_3323 : Nat.Prime 3323 := by norm_num
private theorem prime_sixtyOneBG_3361 : Nat.Prime 3361 := by norm_num
private theorem prime_sixtyOneBG_3457 : Nat.Prime 3457 := by norm_num
private theorem prime_sixtyOneBG_3491 : Nat.Prime 3491 := by norm_num
private theorem prime_sixtyOneBG_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_sixtyOneBG_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_sixtyOneBG_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_sixtyOneBG_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_sixtyOneBG_3797 : Nat.Prime 3797 := by norm_num
private theorem prime_sixtyOneBG_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_sixtyOneBG_4021 : Nat.Prime 4021 := by norm_num
private theorem prime_sixtyOneBG_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_sixtyOneBG_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_sixtyOneBG_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_sixtyOneBG_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_sixtyOneBG_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_sixtyOneBG_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_sixtyOneBG_4441 : Nat.Prime 4441 := by norm_num
private theorem prime_sixtyOneBG_4547 : Nat.Prime 4547 := by norm_num
private theorem prime_sixtyOneBG_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_sixtyOneBG_5281 : Nat.Prime 5281 := by norm_num
private theorem prime_sixtyOneBG_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_sixtyOneBG_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_sixtyOneBG_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_sixtyOneBG_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_sixtyOneBG_6067 : Nat.Prime 6067 := by norm_num
private theorem prime_sixtyOneBG_6133 : Nat.Prime 6133 := by norm_num
private theorem prime_sixtyOneBG_6143 : Nat.Prime 6143 := by norm_num
private theorem prime_sixtyOneBG_6373 : Nat.Prime 6373 := by norm_num
private theorem prime_sixtyOneBG_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_sixtyOneBG_6703 : Nat.Prime 6703 := by norm_num
private theorem prime_sixtyOneBG_6827 : Nat.Prime 6827 := by norm_num
private theorem prime_sixtyOneBG_6883 : Nat.Prime 6883 := by norm_num
private theorem prime_sixtyOneBG_6917 : Nat.Prime 6917 := by norm_num
private theorem prime_sixtyOneBG_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_sixtyOneBG_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_sixtyOneBG_7433 : Nat.Prime 7433 := by norm_num
private theorem prime_sixtyOneBG_7547 : Nat.Prime 7547 := by norm_num
private theorem prime_sixtyOneBG_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_sixtyOneBG_7829 : Nat.Prime 7829 := by norm_num
private theorem prime_sixtyOneBG_7867 : Nat.Prime 7867 := by norm_num
private theorem prime_sixtyOneBG_8123 : Nat.Prime 8123 := by norm_num
private theorem prime_sixtyOneBG_8243 : Nat.Prime 8243 := by norm_num
private theorem prime_sixtyOneBG_8273 : Nat.Prime 8273 := by norm_num
private theorem prime_sixtyOneBG_8297 : Nat.Prime 8297 := by norm_num
private theorem prime_sixtyOneBG_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_sixtyOneBG_9521 : Nat.Prime 9521 := by norm_num
private theorem prime_sixtyOneBG_9767 : Nat.Prime 9767 := by norm_num
private theorem prime_sixtyOneBG_9967 : Nat.Prime 9967 := by norm_num
private theorem prime_sixtyOneBG_10061 : Nat.Prime 10061 := by norm_num
private theorem prime_sixtyOneBG_10093 : Nat.Prime 10093 := by norm_num
private theorem prime_sixtyOneBG_10273 : Nat.Prime 10273 := by norm_num
private theorem prime_sixtyOneBG_10343 : Nat.Prime 10343 := by norm_num
private theorem prime_sixtyOneBG_10631 : Nat.Prime 10631 := by norm_num
private theorem prime_sixtyOneBG_10729 : Nat.Prime 10729 := by norm_num
private theorem prime_sixtyOneBG_11329 : Nat.Prime 11329 := by norm_num
private theorem prime_sixtyOneBG_11677 : Nat.Prime 11677 := by norm_num
private theorem prime_sixtyOneBG_11717 : Nat.Prime 11717 := by norm_num
private theorem prime_sixtyOneBG_11813 : Nat.Prime 11813 := by norm_num
private theorem prime_sixtyOneBG_11909 : Nat.Prime 11909 := by norm_num
private theorem prime_sixtyOneBG_12143 : Nat.Prime 12143 := by norm_num
private theorem prime_sixtyOneBG_12157 : Nat.Prime 12157 := by norm_num
private theorem prime_sixtyOneBG_14293 : Nat.Prime 14293 := by norm_num
private theorem prime_sixtyOneBG_14549 : Nat.Prime 14549 := by norm_num
private theorem prime_sixtyOneBG_14797 : Nat.Prime 14797 := by norm_num
private theorem prime_sixtyOneBG_15667 : Nat.Prime 15667 := by norm_num
private theorem prime_sixtyOneBG_16693 : Nat.Prime 16693 := by norm_num
private theorem prime_sixtyOneBG_17209 : Nat.Prime 17209 := by norm_num
private theorem prime_sixtyOneBG_17317 : Nat.Prime 17317 := by norm_num
private theorem prime_sixtyOneBG_17383 : Nat.Prime 17383 := by norm_num
private theorem prime_sixtyOneBG_18121 : Nat.Prime 18121 := by norm_num
private theorem prime_sixtyOneBG_19543 : Nat.Prime 19543 := by norm_num
private theorem prime_sixtyOneBG_20051 : Nat.Prime 20051 := by norm_num
private theorem prime_sixtyOneBG_21773 : Nat.Prime 21773 := by norm_num
private theorem prime_sixtyOneBG_23567 : Nat.Prime 23567 := by norm_num
private theorem prime_sixtyOneBG_25969 : Nat.Prime 25969 := by norm_num
private theorem prime_sixtyOneBG_26083 : Nat.Prime 26083 := by norm_num
private theorem prime_sixtyOneBG_27847 : Nat.Prime 27847 := by norm_num
private theorem prime_sixtyOneBG_28057 : Nat.Prime 28057 := by norm_num
private theorem prime_sixtyOneBG_28927 : Nat.Prime 28927 := by norm_num
private theorem prime_sixtyOneBG_31963 : Nat.Prime 31963 := by norm_num
private theorem prime_sixtyOneBG_32381 : Nat.Prime 32381 := by norm_num
private theorem prime_sixtyOneBG_32713 : Nat.Prime 32713 := by norm_num
private theorem prime_sixtyOneBG_32911 : Nat.Prime 32911 := by norm_num
private theorem prime_sixtyOneBG_39229 : Nat.Prime 39229 := by norm_num
private theorem prime_sixtyOneBG_42373 : Nat.Prime 42373 := by norm_num
private theorem prime_sixtyOneBG_44089 : Nat.Prime 44089 := by norm_num
private theorem prime_sixtyOneBG_46309 : Nat.Prime 46309 := by norm_num
private theorem prime_sixtyOneBG_50849 : Nat.Prime 50849 := by norm_num
private theorem prime_sixtyOneBG_50891 : Nat.Prime 50891 := by norm_num
private theorem prime_sixtyOneBG_51481 : Nat.Prime 51481 := by norm_num
private theorem prime_sixtyOneBG_52177 : Nat.Prime 52177 := by norm_num
private theorem prime_sixtyOneBG_54091 : Nat.Prime 54091 := by norm_num
private theorem prime_sixtyOneBG_57773 : Nat.Prime 57773 := by norm_num
private theorem prime_sixtyOneBG_60623 : Nat.Prime 60623 := by norm_num
private theorem prime_sixtyOneBG_62761 : Nat.Prime 62761 := by norm_num
private theorem prime_sixtyOneBG_69233 : Nat.Prime 69233 := by norm_num
private theorem prime_sixtyOneBG_69383 : Nat.Prime 69383 := by norm_num
private theorem prime_sixtyOneBG_69593 : Nat.Prime 69593 := by norm_num
private theorem prime_sixtyOneBG_70067 : Nat.Prime 70067 := by norm_num
private theorem prime_sixtyOneBG_70241 : Nat.Prime 70241 := by norm_num
private theorem prime_sixtyOneBG_70321 : Nat.Prime 70321 := by norm_num
private theorem prime_sixtyOneBG_79843 : Nat.Prime 79843 := by norm_num
private theorem prime_sixtyOneBG_81943 : Nat.Prime 81943 := by norm_num
private theorem prime_sixtyOneBG_82189 : Nat.Prime 82189 := by norm_num
private theorem prime_sixtyOneBG_82279 : Nat.Prime 82279 := by norm_num
private theorem prime_sixtyOneBG_82939 : Nat.Prime 82939 := by norm_num
private theorem prime_sixtyOneBG_86353 : Nat.Prime 86353 := by norm_num
private theorem prime_sixtyOneBG_92377 : Nat.Prime 92377 := by norm_num
private theorem prime_sixtyOneBG_94169 : Nat.Prime 94169 := by norm_num
private theorem prime_sixtyOneBG_94427 : Nat.Prime 94427 := by norm_num
private theorem prime_sixtyOneBG_99767 : Nat.Prime 99767 := by norm_num
private theorem prime_sixtyOneBG_103483 : Nat.Prime 103483 := by norm_num
private theorem prime_sixtyOneBG_116731 : Nat.Prime 116731 := by norm_num
private theorem prime_sixtyOneBG_117779 : Nat.Prime 117779 := by norm_num
private theorem prime_sixtyOneBG_125101 : Nat.Prime 125101 := by norm_num
private theorem prime_sixtyOneBG_128549 : Nat.Prime 128549 := by norm_num
private theorem prime_sixtyOneBG_128981 : Nat.Prime 128981 := by norm_num
private theorem prime_sixtyOneBG_129593 : Nat.Prime 129593 := by norm_num
private theorem prime_sixtyOneBG_130693 : Nat.Prime 130693 := by norm_num
private theorem prime_sixtyOneBG_131849 : Nat.Prime 131849 := by norm_num
private theorem prime_sixtyOneBG_132529 : Nat.Prime 132529 := by norm_num
private theorem prime_sixtyOneBG_141853 : Nat.Prime 141853 := by norm_num
private theorem prime_sixtyOneBG_142907 : Nat.Prime 142907 := by norm_num
private theorem prime_sixtyOneBG_156677 : Nat.Prime 156677 := by norm_num
private theorem prime_sixtyOneBG_157327 : Nat.Prime 157327 := by norm_num
private theorem prime_sixtyOneBG_159407 : Nat.Prime 159407 := by norm_num
private theorem prime_sixtyOneBG_159589 : Nat.Prime 159589 := by norm_num
private theorem prime_sixtyOneBG_163909 : Nat.Prime 163909 := by norm_num
private theorem prime_sixtyOneBG_165883 : Nat.Prime 165883 := by norm_num
private theorem prime_sixtyOneBG_167033 : Nat.Prime 167033 := by norm_num
private theorem prime_sixtyOneBG_174481 : Nat.Prime 174481 := by norm_num
private theorem prime_sixtyOneBG_184631 : Nat.Prime 184631 := by norm_num
private theorem prime_sixtyOneBG_188431 : Nat.Prime 188431 := by norm_num
private theorem prime_sixtyOneBG_193247 : Nat.Prime 193247 := by norm_num
private theorem prime_sixtyOneBG_193601 : Nat.Prime 193601 := by norm_num
private theorem prime_sixtyOneBG_198221 : Nat.Prime 198221 := by norm_num
private theorem prime_sixtyOneBG_201709 : Nat.Prime 201709 := by norm_num
private theorem prime_sixtyOneBG_207227 : Nat.Prime 207227 := by norm_num
private theorem prime_sixtyOneBG_214133 : Nat.Prime 214133 := by norm_num
private theorem prime_sixtyOneBG_221957 : Nat.Prime 221957 := by norm_num
private theorem prime_sixtyOneBG_231947 : Nat.Prime 231947 := by norm_num
private theorem prime_sixtyOneBG_273929 : Nat.Prime 273929 := by norm_num
private theorem prime_sixtyOneBG_301759 : Nat.Prime 301759 := by norm_num
private theorem prime_sixtyOneBG_323647 : Nat.Prime 323647 := by norm_num
private theorem prime_sixtyOneBG_328781 : Nat.Prime 328781 := by norm_num
private theorem prime_sixtyOneBG_333503 : Nat.Prime 333503 := by norm_num
private theorem prime_sixtyOneBG_338119 : Nat.Prime 338119 := by norm_num
private theorem prime_sixtyOneBG_348209 : Nat.Prime 348209 := by norm_num
private theorem prime_sixtyOneBG_351653 : Nat.Prime 351653 := by norm_num
private theorem prime_sixtyOneBG_387679 : Nat.Prime 387679 := by norm_num
private theorem prime_sixtyOneBG_391889 : Nat.Prime 391889 := by norm_num
private theorem prime_sixtyOneBG_392389 : Nat.Prime 392389 := by norm_num
private theorem prime_sixtyOneBG_399271 : Nat.Prime 399271 := by norm_num
private theorem prime_sixtyOneBG_416243 : Nat.Prime 416243 := by norm_num
private theorem prime_sixtyOneBG_461233 : Nat.Prime 461233 := by norm_num
private theorem prime_sixtyOneBG_474983 : Nat.Prime 474983 := by norm_num
private theorem prime_sixtyOneBG_479267 : Nat.Prime 479267 := by norm_num
private theorem prime_sixtyOneBG_502093 : Nat.Prime 502093 := by norm_num
private theorem prime_sixtyOneBG_549863 : Nat.Prime 549863 := by norm_num
private theorem prime_sixtyOneBG_571477 : Nat.Prime 571477 := by norm_num
private theorem prime_sixtyOneBG_579763 : Nat.Prime 579763 := by norm_num
private theorem prime_sixtyOneBG_583697 : Nat.Prime 583697 := by norm_num
private theorem prime_sixtyOneBG_681977 : Nat.Prime 681977 := by norm_num
private theorem prime_sixtyOneBG_688717 : Nat.Prime 688717 := by norm_num
private theorem prime_sixtyOneBG_694511 : Nat.Prime 694511 := by norm_num
private theorem prime_sixtyOneBG_699187 : Nat.Prime 699187 := by norm_num
private theorem prime_sixtyOneBG_787331 : Nat.Prime 787331 := by norm_num
private theorem prime_sixtyOneBG_791891 : Nat.Prime 791891 := by norm_num
private theorem prime_sixtyOneBG_836071 : Nat.Prime 836071 := by norm_num
private theorem prime_sixtyOneBG_847703 : Nat.Prime 847703 := by norm_num
private theorem prime_sixtyOneBG_912511 : Nat.Prime 912511 := by norm_num
private theorem prime_sixtyOneBG_930301 : Nat.Prime 930301 := by norm_num
private theorem prime_sixtyOneBG_993781 : Nat.Prime 993781 := by norm_num
private theorem prime_sixtyOneBG_1009807 : Nat.Prime 1009807 := by norm_num
private theorem prime_sixtyOneBG_1016453 : Nat.Prime 1016453 := by norm_num
private theorem prime_sixtyOneBG_1045841 : Nat.Prime 1045841 := by norm_num
private theorem prime_sixtyOneBG_1094773 : Nat.Prime 1094773 := by norm_num
private theorem prime_sixtyOneBG_1182289 : Nat.Prime 1182289 := by norm_num
private theorem prime_sixtyOneBG_1189471 : Nat.Prime 1189471 := by norm_num
private theorem prime_sixtyOneBG_1216277 : Nat.Prime 1216277 := by norm_num
private theorem prime_sixtyOneBG_1286011 : Nat.Prime 1286011 := by norm_num
private theorem prime_sixtyOneBG_1419371 : Nat.Prime 1419371 := by norm_num
private theorem prime_sixtyOneBG_1789163 : Nat.Prime 1789163 := by norm_num
private theorem prime_sixtyOneBG_1815179 : Nat.Prime 1815179 := by norm_num
private theorem prime_sixtyOneBG_1895273 : Nat.Prime 1895273 := by norm_num
private theorem prime_sixtyOneBG_1898629 : Nat.Prime 1898629 := by norm_num
private theorem prime_sixtyOneBG_1902779 : Nat.Prime 1902779 := by norm_num
private theorem prime_sixtyOneBG_2028391 : Nat.Prime 2028391 := by norm_num
private theorem prime_sixtyOneBG_2030009 : Nat.Prime 2030009 := by norm_num
private theorem prime_sixtyOneBG_2066293 : Nat.Prime 2066293 := by norm_num
private theorem prime_sixtyOneBG_2072029 : Nat.Prime 2072029 := by norm_num
private theorem prime_sixtyOneBG_2089169 : Nat.Prime 2089169 := by norm_num
private theorem prime_sixtyOneBG_2125841 : Nat.Prime 2125841 := by norm_num
private theorem prime_sixtyOneBG_2146043 : Nat.Prime 2146043 := by norm_num
private theorem prime_sixtyOneBG_2210347 : Nat.Prime 2210347 := by norm_num
private theorem prime_sixtyOneBG_2240723 : Nat.Prime 2240723 := by norm_num
private theorem prime_sixtyOneBG_2450131 : Nat.Prime 2450131 := by norm_num
private theorem prime_sixtyOneBG_2548877 : Nat.Prime 2548877 := by norm_num
private theorem prime_sixtyOneBG_2707897 : Nat.Prime 2707897 := by norm_num
private theorem prime_sixtyOneBG_2738783 : Nat.Prime 2738783 := by norm_num
private theorem prime_sixtyOneBG_2784491 : Nat.Prime 2784491 := by norm_num
private theorem prime_sixtyOneBG_2957947 : Nat.Prime 2957947 := by norm_num
private theorem prime_sixtyOneBG_3090697 : Nat.Prime 3090697 := by norm_num
private theorem prime_sixtyOneBG_3310877 : Nat.Prime 3310877 := by norm_num
private theorem prime_sixtyOneBG_3487189 : Nat.Prime 3487189 := by norm_num
private theorem prime_sixtyOneBG_3724379 : Nat.Prime 3724379 := by norm_num
private theorem prime_sixtyOneBG_3748079 : Nat.Prime 3748079 := by norm_num
private theorem prime_sixtyOneBG_3880847 : Nat.Prime 3880847 := by norm_num
private theorem prime_sixtyOneBG_4107263 : Nat.Prime 4107263 := by norm_num
private theorem prime_sixtyOneBG_4297453 : Nat.Prime 4297453 := by norm_num
private theorem prime_sixtyOneBG_4728799 : Nat.Prime 4728799 := by norm_num
private theorem prime_sixtyOneBG_4777781 : Nat.Prime 4777781 := by norm_num
private theorem prime_sixtyOneBG_4777789 : Nat.Prime 4777789 := by norm_num
private theorem prime_sixtyOneBG_4797781 : Nat.Prime 4797781 := by norm_num
private theorem prime_sixtyOneBG_5028607 : Nat.Prime 5028607 := by norm_num
private theorem prime_sixtyOneBG_5232317 : Nat.Prime 5232317 := by norm_num
private theorem prime_sixtyOneBG_5242807 : Nat.Prime 5242807 := by norm_num
private theorem prime_sixtyOneBG_5309443 : Nat.Prime 5309443 := by norm_num
private theorem prime_sixtyOneBG_5311499 : Nat.Prime 5311499 := by norm_num
private theorem prime_sixtyOneBG_5619703 : Nat.Prime 5619703 := by norm_num
private theorem prime_sixtyOneBG_5717891 : Nat.Prime 5717891 := by norm_num
private theorem prime_sixtyOneBG_5788423 : Nat.Prime 5788423 := by norm_num
private theorem prime_sixtyOneBG_5830007 : Nat.Prime 5830007 := by norm_num
private theorem prime_sixtyOneBG_5946023 : Nat.Prime 5946023 := by norm_num
private theorem prime_sixtyOneBG_5995009 : Nat.Prime 5995009 := by norm_num
private theorem prime_sixtyOneBG_6264781 : Nat.Prime 6264781 := by norm_num
private theorem prime_sixtyOneBG_6364339 : Nat.Prime 6364339 := by norm_num
private theorem prime_sixtyOneBG_6981391 : Nat.Prime 6981391 := by norm_num
private theorem prime_sixtyOneBG_7447267 : Nat.Prime 7447267 := by norm_num
private theorem prime_sixtyOneBG_7607317 : Nat.Prime 7607317 := by norm_num
private theorem prime_sixtyOneBG_8015141 : Nat.Prime 8015141 := by norm_num
private theorem prime_sixtyOneBG_8034049 : Nat.Prime 8034049 := by norm_num
private theorem prime_sixtyOneBG_8052073 : Nat.Prime 8052073 := by norm_num
private theorem prime_sixtyOneBG_8466043 : Nat.Prime 8466043 := by norm_num
private theorem prime_sixtyOneBG_8634161 : Nat.Prime 8634161 := by norm_num
private theorem prime_sixtyOneBG_9006373 : Nat.Prime 9006373 := by norm_num
private theorem prime_sixtyOneBG_9211919 : Nat.Prime 9211919 := by norm_num
private theorem prime_sixtyOneBG_9370337 : Nat.Prime 9370337 := by norm_num
private theorem prime_sixtyOneBG_10017989 : Nat.Prime 10017989 := by norm_num
private theorem prime_sixtyOneBG_10425409 : Nat.Prime 10425409 := by norm_num
private theorem prime_sixtyOneBG_11678753 : Nat.Prime 11678753 := by norm_num
private theorem prime_sixtyOneBG_11726731 : Nat.Prime 11726731 := by norm_num
private theorem prime_sixtyOneBG_12234913 : Nat.Prime 12234913 := by norm_num
private theorem prime_sixtyOneBG_13435141 : Nat.Prime 13435141 := by norm_num
private theorem prime_sixtyOneBG_15237631 : Nat.Prime 15237631 := by norm_num
private theorem prime_sixtyOneBG_15468737 : Nat.Prime 15468737 := by norm_num
private theorem prime_sixtyOneBG_17995391 : Nat.Prime 17995391 := by norm_num
private theorem prime_sixtyOneBG_18106661 : Nat.Prime 18106661 := by norm_num
private theorem prime_sixtyOneBG_18559577 : Nat.Prime 18559577 := by norm_num
private theorem prime_sixtyOneBG_19465079 : Nat.Prime 19465079 := by norm_num
private theorem prime_sixtyOneBG_20749831 : Nat.Prime 20749831 := by norm_num
private theorem prime_sixtyOneBG_21286541 : Nat.Prime 21286541 := by norm_num
private theorem prime_sixtyOneBG_21797203 : Nat.Prime 21797203 := by norm_num
private theorem prime_sixtyOneBG_21805963 : Nat.Prime 21805963 := by norm_num
private theorem prime_sixtyOneBG_23438953 : Nat.Prime 23438953 := by norm_num
private theorem prime_sixtyOneBG_23602933 : Nat.Prime 23602933 := by norm_num
private theorem prime_sixtyOneBG_24034841 : Nat.Prime 24034841 := by norm_num
private theorem prime_sixtyOneBG_24423701 : Nat.Prime 24423701 := by norm_num
private theorem prime_sixtyOneBG_25011671 : Nat.Prime 25011671 := by norm_num
private theorem prime_sixtyOneBG_29913953 : Nat.Prime 29913953 := by norm_num
private theorem prime_sixtyOneBG_30640249 : Nat.Prime 30640249 := by
  apply lucas_primality 30640249 (7 : ZMod 30640249)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (141853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (141853, 1)] : List FactorBlock).map factorBlockValue).prod) = 30640249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_141853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 30640249) ^ 15320124 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30640249) ^ 10213416 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30640249) ^ 216 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_32519029 : Nat.Prime 32519029 := by
  apply lucas_primality 32519029 (6 : ZMod 32519029)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (159407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (159407, 1)] : List FactorBlock).map factorBlockValue).prod) = 32519029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_159407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 32519029) ^ 16259514 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 32519029) ^ 10839676 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 32519029) ^ 1912884 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 32519029) ^ 204 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_32781097 : Nat.Prime 32781097 := by
  apply lucas_primality 32781097 (10 : ZMod 32781097)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (109, 1), (4177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (109, 1), (4177, 1)] : List FactorBlock).map factorBlockValue).prod) = 32781097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_109
      · exact prime_sixtyOneBG_4177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 32781097) ^ 16390548 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 32781097) ^ 10927032 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 32781097) ^ 300744 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 32781097) ^ 7848 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_36945031 : Nat.Prime 36945031 := by
  apply lucas_primality 36945031 (3 : ZMod 36945031)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (863, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (863, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) = 36945031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_863
      · exact prime_sixtyOneBG_1427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36945031) ^ 18472515 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 36945031) ^ 12315010 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 36945031) ^ 7389006 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 36945031) ^ 42810 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 36945031) ^ 25890 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_38543941 : Nat.Prime 38543941 := by
  apply lucas_primality 38543941 (2 : ZMod 38543941)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (214133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (214133, 1)] : List FactorBlock).map factorBlockValue).prod) = 38543941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_214133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38543941) ^ 19271970 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 38543941) ^ 12847980 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 38543941) ^ 7708788 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 38543941) ^ 180 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_46784809 : Nat.Prime 46784809 := by
  apply lucas_primality 46784809 (13 : ZMod 46784809)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (89, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (89, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 46784809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_89
      · exact prime_sixtyOneBG_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 46784809) ^ 23392404 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 46784809) ^ 15594936 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 46784809) ^ 6683544 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 46784809) ^ 525672 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 46784809) ^ 313992 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_47515913 : Nat.Prime 47515913 := by
  apply lucas_primality 47515913 (3 : ZMod 47515913)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (787, 1), (7547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (787, 1), (7547, 1)] : List FactorBlock).map factorBlockValue).prod) = 47515913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_787
      · exact prime_sixtyOneBG_7547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47515913) ^ 23757956 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 47515913) ^ 60376 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 47515913) ^ 6296 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_48874043 : Nat.Prime 48874043 := by
  apply lucas_primality 48874043 (2 : ZMod 48874043)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (31, 1), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (31, 1), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) = 48874043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_31
      · exact prime_sixtyOneBG_5927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48874043) ^ 24437021 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48874043) ^ 6982006 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48874043) ^ 2572318 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48874043) ^ 1576582 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48874043) ^ 8246 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_51316429 : Nat.Prime 51316429 := by
  apply lucas_primality 51316429 (11 : ZMod 51316429)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (167, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (167, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 51316429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_167
      · exact prime_sixtyOneBG_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 51316429) ^ 25658214 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 51316429) ^ 17105476 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 51316429) ^ 1769532 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 51316429) ^ 307284 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 51316429) ^ 58116 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_52185857 : Nat.Prime 52185857 := by
  apply lucas_primality 52185857 (3 : ZMod 52185857)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (19, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (19, 1), (10729, 1)] : List FactorBlock).map factorBlockValue).prod) = 52185857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_10729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 52185857) ^ 26092928 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 52185857) ^ 2746624 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 52185857) ^ 4864 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_53011601 : Nat.Prime 53011601 := by
  apply lucas_primality 53011601 (3 : ZMod 53011601)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (132529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (132529, 1)] : List FactorBlock).map factorBlockValue).prod) = 53011601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_132529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53011601) ^ 26505800 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 53011601) ^ 10602320 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 53011601) ^ 400 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_57852229 : Nat.Prime 57852229 := by
  apply lucas_primality 57852229 (6 : ZMod 57852229)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (688717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (688717, 1)] : List FactorBlock).map factorBlockValue).prod) = 57852229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_688717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 57852229) ^ 28926114 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 57852229) ^ 19284076 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 57852229) ^ 8264604 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 57852229) ^ 84 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_59827907 : Nat.Prime 59827907 := by
  apply lucas_primality 59827907 (2 : ZMod 59827907)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29913953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29913953, 1)] : List FactorBlock).map factorBlockValue).prod) = 59827907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_29913953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 59827907) ^ 29913953 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59827907) ^ 2 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_61728529 : Nat.Prime 61728529 := by
  apply lucas_primality 61728529 (19 : ZMod 61728529)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1286011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1286011, 1)] : List FactorBlock).map factorBlockValue).prod) = 61728529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_1286011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 61728529) ^ 30864264 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 61728529) ^ 20576176 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 61728529) ^ 48 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_64564447 : Nat.Prime 64564447 := by
  apply lucas_primality 64564447 (6 : ZMod 64564447)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2837, 1), (3793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2837, 1), (3793, 1)] : List FactorBlock).map factorBlockValue).prod) = 64564447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_2837
      · exact prime_sixtyOneBG_3793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 64564447) ^ 32282223 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 64564447) ^ 21521482 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 64564447) ^ 22758 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 64564447) ^ 17022 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_65789569 : Nat.Prime 65789569 := by
  apply lucas_primality 65789569 (11 : ZMod 65789569)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (13, 1), (23, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (13, 1), (23, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 65789569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 65789569) ^ 32894784 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 65789569) ^ 21929856 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 65789569) ^ 5060736 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 65789569) ^ 2860416 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 65789569) ^ 344448 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_68192419 : Nat.Prime 68192419 := by
  apply lucas_primality 68192419 (3 : ZMod 68192419)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (231947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (231947, 1)] : List FactorBlock).map factorBlockValue).prod) = 68192419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_231947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 68192419) ^ 34096209 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68192419) ^ 22730806 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68192419) ^ 9741774 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68192419) ^ 294 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_69813911 : Nat.Prime 69813911 := by
  apply lucas_primality 69813911 (13 : ZMod 69813911)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6981391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6981391, 1)] : List FactorBlock).map factorBlockValue).prod) = 69813911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_6981391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 69813911) ^ 34906955 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 69813911) ^ 13962782 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 69813911) ^ 10 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_75485071 : Nat.Prime 75485071 := by
  apply lucas_primality 75485071 (3 : ZMod 75485071)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (71, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (71, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) = 75485071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_71
      · exact prime_sixtyOneBG_11813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75485071) ^ 37742535 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 75485071) ^ 25161690 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 75485071) ^ 15097014 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 75485071) ^ 1063170 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 75485071) ^ 6390 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_82996471 : Nat.Prime 82996471 := by
  apply lucas_primality 82996471 (3 : ZMod 82996471)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (229, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (229, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) = 82996471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_229
      · exact prime_sixtyOneBG_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 82996471) ^ 41498235 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 82996471) ^ 27665490 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 82996471) ^ 16599294 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 82996471) ^ 362430 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 82996471) ^ 20610 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_84660431 : Nat.Prime 84660431 := by
  apply lucas_primality 84660431 (7 : ZMod 84660431)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (8466043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (8466043, 1)] : List FactorBlock).map factorBlockValue).prod) = 84660431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_8466043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 84660431) ^ 42330215 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 84660431) ^ 16932086 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 84660431) ^ 10 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_88718293 : Nat.Prime 88718293 := by
  apply lucas_primality 88718293 (2 : ZMod 88718293)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (163, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (163, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) = 88718293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_163
      · exact prime_sixtyOneBG_1163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88718293) ^ 44359146 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 88718293) ^ 29572764 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 88718293) ^ 6824484 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 88718293) ^ 544284 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 88718293) ^ 76284 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_90235247 : Nat.Prime 90235247 := by
  apply lucas_primality 90235247 (5 : ZMod 90235247)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (399271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (399271, 1)] : List FactorBlock).map factorBlockValue).prod) = 90235247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_113
      · exact prime_sixtyOneBG_399271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 90235247) ^ 45117623 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 90235247) ^ 798542 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 90235247) ^ 226 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_102905503 : Nat.Prime 102905503 := by
  apply lucas_primality 102905503 (5 : ZMod 102905503)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2450131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2450131, 1)] : List FactorBlock).map factorBlockValue).prod) = 102905503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_2450131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102905503) ^ 51452751 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 102905503) ^ 34301834 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 102905503) ^ 14700786 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 102905503) ^ 42 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_103133669 : Nat.Prime 103133669 := by
  apply lucas_primality 103133669 (2 : ZMod 103133669)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (997, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (997, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) = 103133669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_997
      · exact prime_sixtyOneBG_2351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103133669) ^ 51566834 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103133669) ^ 9375788 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103133669) ^ 103444 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 103133669) ^ 43868 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_104524261 : Nat.Prime 104524261 := by
  apply lucas_primality 104524261 (2 : ZMod 104524261)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (197, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (197, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 104524261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_37
      · exact prime_sixtyOneBG_197
      · exact prime_sixtyOneBG_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104524261) ^ 52262130 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 104524261) ^ 34841420 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 104524261) ^ 20904852 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 104524261) ^ 2824980 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 104524261) ^ 530580 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 104524261) ^ 437340 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_104840297 : Nat.Prime 104840297 := by
  apply lucas_primality 104840297 (3 : ZMod 104840297)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (163, 1), (7309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (163, 1), (7309, 1)] : List FactorBlock).map factorBlockValue).prod) = 104840297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_163
      · exact prime_sixtyOneBG_7309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 104840297) ^ 52420148 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 104840297) ^ 9530936 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 104840297) ^ 643192 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 104840297) ^ 14344 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_108343717 : Nat.Prime 108343717 := by
  apply lucas_primality 108343717 (5 : ZMod 108343717)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (694511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (694511, 1)] : List FactorBlock).map factorBlockValue).prod) = 108343717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_694511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 108343717) ^ 54171858 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 108343717) ^ 36114572 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 108343717) ^ 8334132 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 108343717) ^ 156 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_110339531 : Nat.Prime 110339531 := by
  apply lucas_primality 110339531 (2 : ZMod 110339531)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (89, 2), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (89, 2), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 110339531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_89
      · exact prime_sixtyOneBG_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 110339531) ^ 55169765 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110339531) ^ 22067906 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110339531) ^ 15762790 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110339531) ^ 1239770 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110339531) ^ 554470 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_118271653 : Nat.Prime 118271653 := by
  apply lucas_primality 118271653 (6 : ZMod 118271653)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (579763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (579763, 1)] : List FactorBlock).map factorBlockValue).prod) = 118271653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_579763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 118271653) ^ 59135826 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 118271653) ^ 39423884 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 118271653) ^ 6957156 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 118271653) ^ 204 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_129474229 : Nat.Prime 129474229 := by
  apply lucas_primality 129474229 (7 : ZMod 129474229)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (31, 1), (41, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (31, 1), (41, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 129474229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_31
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 129474229) ^ 64737114 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 129474229) ^ 43158076 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 129474229) ^ 9959556 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 129474229) ^ 4176588 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 129474229) ^ 3157908 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 129474229) ^ 198276 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_132441233 : Nat.Prime 132441233 := by
  apply lucas_primality 132441233 (3 : ZMod 132441233)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (193, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (193, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) = 132441233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_193
      · exact prime_sixtyOneBG_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 132441233) ^ 66220616 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 132441233) ^ 18920176 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 132441233) ^ 12040112 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 132441233) ^ 686224 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 132441233) ^ 237776 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_140633719 : Nat.Prime 140633719 := by
  apply lucas_primality 140633719 (3 : ZMod 140633719)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23438953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23438953, 1)] : List FactorBlock).map factorBlockValue).prod) = 140633719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_23438953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 140633719) ^ 70316859 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 140633719) ^ 46877906 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 140633719) ^ 6 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_201593081 : Nat.Prime 201593081 := by
  apply lucas_primality 201593081 (3 : ZMod 201593081)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (387679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (387679, 1)] : List FactorBlock).map factorBlockValue).prod) = 201593081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_387679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 201593081) ^ 100796540 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 201593081) ^ 40318616 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 201593081) ^ 15507160 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 201593081) ^ 520 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_213095521 : Nat.Prime 213095521 := by
  apply lucas_primality 213095521 (13 : ZMod 213095521)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (11, 2), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (11, 2), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) = 213095521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_1223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 213095521) ^ 106547760 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 213095521) ^ 71031840 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 213095521) ^ 42619104 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 213095521) ^ 19372320 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 213095521) ^ 174240 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_213455131 : Nat.Prime 213455131 := by
  apply lucas_primality 213455131 (2 : ZMod 213455131)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1016453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1016453, 1)] : List FactorBlock).map factorBlockValue).prod) = 213455131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_1016453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 213455131) ^ 106727565 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 213455131) ^ 71151710 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 213455131) ^ 42691026 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 213455131) ^ 30493590 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 213455131) ^ 210 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_232067249 : Nat.Prime 232067249 := by
  apply lucas_primality 232067249 (3 : ZMod 232067249)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2072029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2072029, 1)] : List FactorBlock).map factorBlockValue).prod) = 232067249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_2072029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 232067249) ^ 116033624 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 232067249) ^ 33152464 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 232067249) ^ 112 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_324054151 : Nat.Prime 324054151 := by
  apply lucas_primality 324054151 (3 : ZMod 324054151)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 2), (44089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 2), (44089, 1)] : List FactorBlock).map factorBlockValue).prod) = 324054151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_44089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 324054151) ^ 162027075 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 324054151) ^ 108018050 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 324054151) ^ 64810830 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 324054151) ^ 46293450 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 324054151) ^ 7350 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_420334793 : Nat.Prime 420334793 := by
  apply lucas_primality 420334793 (3 : ZMod 420334793)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (3090697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (3090697, 1)] : List FactorBlock).map factorBlockValue).prod) = 420334793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_3090697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 420334793) ^ 210167396 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 420334793) ^ 24725576 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 420334793) ^ 136 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_486041539 : Nat.Prime 486041539 := by
  apply lucas_primality 486041539 (2 : ZMod 486041539)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2909, 1), (27847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2909, 1), (27847, 1)] : List FactorBlock).map factorBlockValue).prod) = 486041539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_2909
      · exact prime_sixtyOneBG_27847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 486041539) ^ 243020769 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 486041539) ^ 162013846 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 486041539) ^ 167082 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 486041539) ^ 17454 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_513164291 : Nat.Prime 513164291 := by
  apply lucas_primality 513164291 (2 : ZMod 513164291)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (51316429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (51316429, 1)] : List FactorBlock).map factorBlockValue).prod) = 513164291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_51316429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 513164291) ^ 256582145 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 513164291) ^ 102632858 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 513164291) ^ 10 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_517896917 : Nat.Prime 517896917 := by
  apply lucas_primality 517896917 (2 : ZMod 517896917)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (129474229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (129474229, 1)] : List FactorBlock).map factorBlockValue).prod) = 517896917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_129474229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 517896917) ^ 258948458 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 517896917) ^ 4 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_522988033 : Nat.Prime 522988033 := by
  apply lucas_primality 522988033 (11 : ZMod 522988033)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (7, 1), (127, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (7, 1), (127, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 522988033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_127
      · exact prime_sixtyOneBG_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 522988033) ^ 261494016 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 522988033) ^ 174329344 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 522988033) ^ 74712576 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 522988033) ^ 4118016 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 522988033) ^ 1365504 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_542193793 : Nat.Prime 542193793 := by
  apply lucas_primality 542193793 (13 : ZMod 542193793)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (201709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (201709, 1)] : List FactorBlock).map factorBlockValue).prod) = 542193793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_201709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 542193793) ^ 271096896 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 542193793) ^ 180731264 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 542193793) ^ 77456256 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 542193793) ^ 2688 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_592144151 : Nat.Prime 592144151 := by
  apply lucas_primality 592144151 (7 : ZMod 592144151)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (857, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (857, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 592144151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_857
      · exact prime_sixtyOneBG_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 592144151) ^ 296072075 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 592144151) ^ 118428830 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 592144151) ^ 45549550 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 592144151) ^ 690950 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 592144151) ^ 557050 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_622664957 : Nat.Prime 622664957 := by
  apply lucas_primality 622664957 (2 : ZMod 622664957)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (787, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (787, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) = 622664957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_139
      · exact prime_sixtyOneBG_787
      · exact prime_sixtyOneBG_1423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 622664957) ^ 311332478 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 622664957) ^ 4479604 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 622664957) ^ 791188 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 622664957) ^ 437572 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_653995723 : Nat.Prime 653995723 := by
  apply lucas_primality 653995723 (2 : ZMod 653995723)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (683, 1), (159589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (683, 1), (159589, 1)] : List FactorBlock).map factorBlockValue).prod) = 653995723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_683
      · exact prime_sixtyOneBG_159589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 653995723) ^ 326997861 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 653995723) ^ 217998574 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 653995723) ^ 957534 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 653995723) ^ 4098 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_673740619 : Nat.Prime 673740619 := by
  apply lucas_primality 673740619 (2 : ZMod 673740619)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (2738783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (2738783, 1)] : List FactorBlock).map factorBlockValue).prod) = 673740619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_2738783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 673740619) ^ 336870309 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 673740619) ^ 224580206 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 673740619) ^ 16432698 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 673740619) ^ 246 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_700931027 : Nat.Prime 700931027 := by
  apply lucas_primality 700931027 (2 : ZMod 700931027)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (15237631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (15237631, 1)] : List FactorBlock).map factorBlockValue).prod) = 700931027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_15237631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 700931027) ^ 350465513 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 700931027) ^ 30475262 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 700931027) ^ 46 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_737102417 : Nat.Prime 737102417 := by
  apply lucas_primality 737102417 (3 : ZMod 737102417)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (83, 1), (131, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (83, 1), (131, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 737102417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_83
      · exact prime_sixtyOneBG_131
      · exact prime_sixtyOneBG_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 737102417) ^ 368551208 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 737102417) ^ 38794864 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 737102417) ^ 8880752 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 737102417) ^ 5626736 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 737102417) ^ 3305392 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_738448379 : Nat.Prime 738448379 := by
  apply lucas_primality 738448379 (2 : ZMod 738448379)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15667, 1), (23567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15667, 1), (23567, 1)] : List FactorBlock).map factorBlockValue).prod) = 738448379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_15667
      · exact prime_sixtyOneBG_23567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 738448379) ^ 369224189 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 738448379) ^ 47134 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 738448379) ^ 31334 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_871995881 : Nat.Prime 871995881 := by
  apply lucas_primality 871995881 (3 : ZMod 871995881)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (19, 1), (163909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (19, 1), (163909, 1)] : List FactorBlock).map factorBlockValue).prod) = 871995881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_163909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 871995881) ^ 435997940 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 871995881) ^ 174399176 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 871995881) ^ 124570840 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 871995881) ^ 45894520 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 871995881) ^ 5320 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_984961069 : Nat.Prime 984961069 := by
  apply lucas_primality 984961069 (2 : ZMod 984961069)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 2), (69383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 2), (69383, 1)] : List FactorBlock).map factorBlockValue).prod) = 984961069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_69383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 984961069) ^ 492480534 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 984961069) ^ 328320356 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 984961069) ^ 140708724 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 984961069) ^ 75766236 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 984961069) ^ 14196 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1125766177 : Nat.Prime 1125766177 := by
  apply lucas_primality 1125766177 (10 : ZMod 1125766177)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11726731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11726731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1125766177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_11726731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1125766177) ^ 562883088 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1125766177) ^ 375255392 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1125766177) ^ 96 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1134997441 : Nat.Prime 1134997441 := by
  apply lucas_primality 1134997441 (11 : ZMod 1134997441)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (1182289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (1182289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1134997441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_1182289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1134997441) ^ 567498720 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1134997441) ^ 378332480 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1134997441) ^ 226999488 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1134997441) ^ 960 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1234866037 : Nat.Prime 1234866037 := by
  apply lucas_primality 1234866037 (2 : ZMod 1234866037)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (102905503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (102905503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1234866037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_102905503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1234866037) ^ 617433018 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1234866037) ^ 411622012 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1234866037) ^ 12 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1560671479 : Nat.Prime 1560671479 := by
  apply lucas_primality 1560671479 (11 : ZMod 1560671479)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (659, 1), (3209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (659, 1), (3209, 1)] : List FactorBlock).map factorBlockValue).prod) = 1560671479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_659
      · exact prime_sixtyOneBG_3209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1560671479) ^ 780335739 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1560671479) ^ 520223826 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1560671479) ^ 38065158 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1560671479) ^ 2368242 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1560671479) ^ 486342 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1573976431 : Nat.Prime 1573976431 := by
  apply lucas_primality 1573976431 (6 : ZMod 1573976431)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 2), (103483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 2), (103483, 1)] : List FactorBlock).map factorBlockValue).prod) = 1573976431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_103483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1573976431) ^ 786988215 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1573976431) ^ 524658810 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1573976431) ^ 314795286 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1573976431) ^ 121075110 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1573976431) ^ 15210 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1678163671 : Nat.Prime 1678163671 := by
  apply lucas_primality 1678163671 (3 : ZMod 1678163671)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (17, 1), (47, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (17, 1), (47, 1), (2593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678163671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_47
      · exact prime_sixtyOneBG_2593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1678163671) ^ 839081835 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678163671) ^ 559387890 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678163671) ^ 335632734 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678163671) ^ 98715510 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678163671) ^ 35705610 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678163671) ^ 647190 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1856406043 : Nat.Prime 1856406043 := by
  apply lucas_primality 1856406043 (2 : ZMod 1856406043)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103133669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103133669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1856406043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_103133669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1856406043) ^ 928203021 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1856406043) ^ 618802014 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1856406043) ^ 18 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1856537993 : Nat.Prime 1856537993 := by
  apply lucas_primality 1856537993 (3 : ZMod 1856537993)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (232067249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (232067249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1856537993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_232067249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1856537993) ^ 928268996 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1856537993) ^ 8 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1863506611 : Nat.Prime 1863506611 := by
  apply lucas_primality 1863506611 (2 : ZMod 1863506611)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (2957947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (2957947, 1)] : List FactorBlock).map factorBlockValue).prod) = 1863506611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_2957947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1863506611) ^ 931753305 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1863506611) ^ 621168870 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1863506611) ^ 372701322 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1863506611) ^ 266215230 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1863506611) ^ 630 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1971595651 : Nat.Prime 1971595651 := by
  apply lucas_primality 1971595651 (2 : ZMod 1971595651)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (23, 1), (571477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (23, 1), (571477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1971595651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_571477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1971595651) ^ 985797825 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971595651) ^ 657198550 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971595651) ^ 394319130 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971595651) ^ 85721550 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971595651) ^ 3450 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2081843299 : Nat.Prime 2081843299 := by
  apply lucas_primality 2081843299 (3 : ZMod 2081843299)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (5028607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (5028607, 1)] : List FactorBlock).map factorBlockValue).prod) = 2081843299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_5028607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2081843299) ^ 1040921649 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2081843299) ^ 693947766 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2081843299) ^ 90514926 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2081843299) ^ 414 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2323901189 : Nat.Prime 2323901189 := by
  apply lucas_primality 2323901189 (2 : ZMod 2323901189)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (82996471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (82996471, 1)] : List FactorBlock).map factorBlockValue).prod) = 2323901189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_82996471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2323901189) ^ 1161950594 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2323901189) ^ 331985884 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2323901189) ^ 28 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2442405071 : Nat.Prime 2442405071 := by
  apply lucas_primality 2442405071 (7 : ZMod 2442405071)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (3457, 1), (10093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (3457, 1), (10093, 1)] : List FactorBlock).map factorBlockValue).prod) = 2442405071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_3457
      · exact prime_sixtyOneBG_10093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2442405071) ^ 1221202535 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2442405071) ^ 488481014 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2442405071) ^ 348915010 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2442405071) ^ 706510 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2442405071) ^ 241990 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2674564667 : Nat.Prime 2674564667 := by
  apply lucas_primality 2674564667 (2 : ZMod 2674564667)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7243, 1), (184631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7243, 1), (184631, 1)] : List FactorBlock).map factorBlockValue).prod) = 2674564667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7243
      · exact prime_sixtyOneBG_184631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2674564667) ^ 1337282333 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2674564667) ^ 369262 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2674564667) ^ 14486 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2844774767 : Nat.Prime 2844774767 := by
  apply lucas_primality 2844774767 (5 : ZMod 2844774767)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (373, 1), (761, 1), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (373, 1), (761, 1), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) = 2844774767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_373
      · exact prime_sixtyOneBG_761
      · exact prime_sixtyOneBG_5011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2844774767) ^ 1422387383 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2844774767) ^ 7626742 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2844774767) ^ 3738206 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2844774767) ^ 567706 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3203421763 : Nat.Prime 3203421763 := by
  apply lucas_primality 3203421763 (5 : ZMod 3203421763)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (419, 1), (769, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (419, 1), (769, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) = 3203421763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_419
      · exact prime_sixtyOneBG_769
      · exact prime_sixtyOneBG_1657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3203421763) ^ 1601710881 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3203421763) ^ 1067807254 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3203421763) ^ 7645398 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3203421763) ^ 4165698 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3203421763) ^ 1933266 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3909579017 : Nat.Prime 3909579017 := by
  apply lucas_primality 3909579017 (3 : ZMod 3909579017)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (69813911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (69813911, 1)] : List FactorBlock).map factorBlockValue).prod) = 3909579017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_69813911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3909579017) ^ 1954789508 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3909579017) ^ 558511288 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3909579017) ^ 56 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3922995239 : Nat.Prime 3922995239 := by
  apply lucas_primality 3922995239 (7 : ZMod 3922995239)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (17995391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (17995391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3922995239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_109
      · exact prime_sixtyOneBG_17995391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3922995239) ^ 1961497619 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3922995239) ^ 35990782 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3922995239) ^ 218 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_4328176141 : Nat.Prime 4328176141 := by
  apply lucas_primality 4328176141 (2 : ZMod 4328176141)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (8015141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (8015141, 1)] : List FactorBlock).map factorBlockValue).prod) = 4328176141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_8015141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4328176141) ^ 2164088070 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4328176141) ^ 1442725380 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4328176141) ^ 865635228 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4328176141) ^ 540 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_4716502529 : Nat.Prime 4716502529 := by
  apply lucas_primality 4716502529 (3 : ZMod 4716502529)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (9211919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (9211919, 1)] : List FactorBlock).map factorBlockValue).prod) = 4716502529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_9211919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4716502529) ^ 2358251264 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4716502529) ^ 512 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_4884810143 : Nat.Prime 4884810143 := by
  apply lucas_primality 4884810143 (5 : ZMod 4884810143)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2442405071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2442405071, 1)] : List FactorBlock).map factorBlockValue).prod) = 4884810143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_2442405071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4884810143) ^ 2442405071 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4884810143) ^ 2 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_5015440267 : Nat.Prime 5015440267 := by
  apply lucas_primality 5015440267 (2 : ZMod 5015440267)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (967, 1), (50849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (967, 1), (50849, 1)] : List FactorBlock).map factorBlockValue).prod) = 5015440267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_967
      · exact prime_sixtyOneBG_50849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5015440267) ^ 2507720133 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5015440267) ^ 1671813422 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5015440267) ^ 295025898 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5015440267) ^ 5186598 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5015440267) ^ 98634 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_6230450183 : Nat.Prime 6230450183 := by
  apply lucas_primality 6230450183 (5 : ZMod 6230450183)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (79, 1), (307, 1), (11677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (79, 1), (307, 1), (11677, 1)] : List FactorBlock).map factorBlockValue).prod) = 6230450183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_79
      · exact prime_sixtyOneBG_307
      · exact prime_sixtyOneBG_11677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6230450183) ^ 3115225091 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6230450183) ^ 566404562 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6230450183) ^ 78866458 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6230450183) ^ 20294626 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6230450183) ^ 533566 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_7316909231 : Nat.Prime 7316909231 := by
  apply lucas_primality 7316909231 (11 : ZMod 7316909231)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (23602933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (23602933, 1)] : List FactorBlock).map factorBlockValue).prod) = 7316909231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_31
      · exact prime_sixtyOneBG_23602933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7316909231) ^ 3658454615 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 7316909231) ^ 1463381846 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 7316909231) ^ 236029330 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 7316909231) ^ 310 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_7683799483 : Nat.Prime 7683799483 := by
  apply lucas_primality 7683799483 (2 : ZMod 7683799483)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (809, 1), (19543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (809, 1), (19543, 1)] : List FactorBlock).map factorBlockValue).prod) = 7683799483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_809
      · exact prime_sixtyOneBG_19543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7683799483) ^ 3841899741 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7683799483) ^ 2561266494 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7683799483) ^ 9497898 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7683799483) ^ 393174 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_7777455811 : Nat.Prime 7777455811 := by
  apply lucas_primality 7777455811 (2 : ZMod 7777455811)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (149, 1), (25969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (149, 1), (25969, 1)] : List FactorBlock).map factorBlockValue).prod) = 7777455811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_67
      · exact prime_sixtyOneBG_149
      · exact prime_sixtyOneBG_25969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7777455811) ^ 3888727905 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7777455811) ^ 2592485270 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7777455811) ^ 1555491162 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7777455811) ^ 116081430 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7777455811) ^ 52197690 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7777455811) ^ 299490 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_8438948047 : Nat.Prime 8438948047 := by
  apply lucas_primality 8438948047 (3 : ZMod 8438948047)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2687, 1), (174481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2687, 1), (174481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8438948047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_2687
      · exact prime_sixtyOneBG_174481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8438948047) ^ 4219474023 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8438948047) ^ 2812982682 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8438948047) ^ 3140658 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8438948047) ^ 48366 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_8461352279 : Nat.Prime 8461352279 := by
  apply lucas_primality 8461352279 (7 : ZMod 8461352279)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32911, 1), (128549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32911, 1), (128549, 1)] : List FactorBlock).map factorBlockValue).prod) = 8461352279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_32911
      · exact prime_sixtyOneBG_128549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8461352279) ^ 4230676139 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8461352279) ^ 257098 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8461352279) ^ 65822 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_8571238411 : Nat.Prime 8571238411 := by
  apply lucas_primality 8571238411 (3 : ZMod 8571238411)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (149, 1), (273929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (149, 1), (273929, 1)] : List FactorBlock).map factorBlockValue).prod) = 8571238411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_149
      · exact prime_sixtyOneBG_273929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8571238411) ^ 4285619205 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571238411) ^ 2857079470 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571238411) ^ 1714247682 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571238411) ^ 1224462630 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571238411) ^ 57525090 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571238411) ^ 31290 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_11776498549 : Nat.Prime 11776498549 := by
  apply lucas_primality 11776498549 (2 : ZMod 11776498549)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 2), (313, 1), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 2), (313, 1), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) = 11776498549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_313
      · exact prime_sixtyOneBG_5927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11776498549) ^ 5888249274 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11776498549) ^ 3925499516 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11776498549) ^ 512021676 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11776498549) ^ 37624596 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11776498549) ^ 1986924 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_12616758487 : Nat.Prime 12616758487 := by
  apply lucas_primality 12616758487 (3 : ZMod 12616758487)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (700931027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (700931027, 1)] : List FactorBlock).map factorBlockValue).prod) = 12616758487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_700931027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12616758487) ^ 6308379243 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12616758487) ^ 4205586162 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12616758487) ^ 18 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_14768967581 : Nat.Prime 14768967581 := by
  apply lucas_primality 14768967581 (2 : ZMod 14768967581)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (738448379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (738448379, 1)] : List FactorBlock).map factorBlockValue).prod) = 14768967581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_738448379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14768967581) ^ 7384483790 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14768967581) ^ 2953793516 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14768967581) ^ 20 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_16157306351 : Nat.Prime 16157306351 := by
  apply lucas_primality 16157306351 (14 : ZMod 16157306351)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (59, 1), (1277, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (59, 1), (1277, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 16157306351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_59
      · exact prime_sixtyOneBG_1277
      · exact prime_sixtyOneBG_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 16157306351) ^ 8078653175 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (14 : ZMod 16157306351) ^ 3231461270 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (14 : ZMod 16157306351) ^ 273852650 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (14 : ZMod 16157306351) ^ 12652550 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (14 : ZMod 16157306351) ^ 3767150 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_17306259263 : Nat.Prime 17306259263 := by
  apply lucas_primality 17306259263 (5 : ZMod 17306259263)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (2411, 1), (10343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (2411, 1), (10343, 1)] : List FactorBlock).map factorBlockValue).prod) = 17306259263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_347
      · exact prime_sixtyOneBG_2411
      · exact prime_sixtyOneBG_10343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17306259263) ^ 8653129631 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17306259263) ^ 49873946 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17306259263) ^ 7178042 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17306259263) ^ 1673234 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_19287079621 : Nat.Prime 19287079621 := by
  apply lucas_primality 19287079621 (6 : ZMod 19287079621)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (67, 1), (4797781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (67, 1), (4797781, 1)] : List FactorBlock).map factorBlockValue).prod) = 19287079621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_67
      · exact prime_sixtyOneBG_4797781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19287079621) ^ 9643539810 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 19287079621) ^ 6429026540 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 19287079621) ^ 3857415924 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 19287079621) ^ 287866860 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 19287079621) ^ 4020 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_19545352249 : Nat.Prime 19545352249 := by
  apply lucas_primality 19545352249 (7 : ZMod 19545352249)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (179, 1), (661, 1), (6883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (179, 1), (661, 1), (6883, 1)] : List FactorBlock).map factorBlockValue).prod) = 19545352249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_179
      · exact prime_sixtyOneBG_661
      · exact prime_sixtyOneBG_6883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19545352249) ^ 9772676124 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19545352249) ^ 6515117416 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19545352249) ^ 109191912 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19545352249) ^ 29569368 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 19545352249) ^ 2839656 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_21123079223 : Nat.Prime 21123079223 := by
  apply lucas_primality 21123079223 (5 : ZMod 21123079223)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1063, 1), (1419371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1063, 1), (1419371, 1)] : List FactorBlock).map factorBlockValue).prod) = 21123079223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_1063
      · exact prime_sixtyOneBG_1419371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21123079223) ^ 10561539611 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21123079223) ^ 3017582746 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21123079223) ^ 19871194 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21123079223) ^ 14882 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_21509579621 : Nat.Prime 21509579621 := by
  apply lucas_primality 21509579621 (2 : ZMod 21509579621)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3323, 1), (323647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3323, 1), (323647, 1)] : List FactorBlock).map factorBlockValue).prod) = 21509579621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_3323
      · exact prime_sixtyOneBG_323647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21509579621) ^ 10754789810 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21509579621) ^ 4301915924 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21509579621) ^ 6472940 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21509579621) ^ 66460 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_25876604297 : Nat.Prime 25876604297 := by
  apply lucas_primality 25876604297 (3 : ZMod 25876604297)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (140633719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (140633719, 1)] : List FactorBlock).map factorBlockValue).prod) = 25876604297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_140633719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25876604297) ^ 12938302148 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 25876604297) ^ 1125069752 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 25876604297) ^ 184 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_36390994349 : Nat.Prime 36390994349 := by
  apply lucas_primality 36390994349 (2 : ZMod 36390994349)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (41, 1), (11678753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (41, 1), (11678753, 1)] : List FactorBlock).map factorBlockValue).prod) = 36390994349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_11678753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36390994349) ^ 18195497174 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36390994349) ^ 1915315492 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36390994349) ^ 887585228 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36390994349) ^ 3116 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_41089200631 : Nat.Prime 41089200631 := by
  apply lucas_primality 41089200631 (3 : ZMod 41089200631)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (2111, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (2111, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) = 41089200631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_83
      · exact prime_sixtyOneBG_2111
      · exact prime_sixtyOneBG_7817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41089200631) ^ 20544600315 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41089200631) ^ 13696400210 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41089200631) ^ 8217840126 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41089200631) ^ 495050610 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41089200631) ^ 19464330 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41089200631) ^ 5256390 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_45004887373 : Nat.Prime 45004887373 := by
  apply lucas_primality 45004887373 (2 : ZMod 45004887373)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (29, 1), (7607317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (29, 1), (7607317, 1)] : List FactorBlock).map factorBlockValue).prod) = 45004887373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_7607317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45004887373) ^ 22502443686 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45004887373) ^ 15001629124 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45004887373) ^ 2647346316 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45004887373) ^ 1551892668 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45004887373) ^ 5916 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_46587798311 : Nat.Prime 46587798311 := by
  apply lucas_primality 46587798311 (13 : ZMod 46587798311)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (108343717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (108343717, 1)] : List FactorBlock).map factorBlockValue).prod) = 46587798311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_43
      · exact prime_sixtyOneBG_108343717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 46587798311) ^ 23293899155 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 46587798311) ^ 9317559662 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 46587798311) ^ 1083437170 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 46587798311) ^ 430 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_46664734867 : Nat.Prime 46664734867 := by
  apply lucas_primality 46664734867 (2 : ZMod 46664734867)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7777455811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7777455811, 1)] : List FactorBlock).map factorBlockValue).prod) = 46664734867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7777455811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46664734867) ^ 23332367433 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46664734867) ^ 15554911622 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46664734867) ^ 6 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_53680487243 : Nat.Prime 53680487243 := by
  apply lucas_primality 53680487243 (2 : ZMod 53680487243)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12143, 1), (2210347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12143, 1), (2210347, 1)] : List FactorBlock).map factorBlockValue).prod) = 53680487243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_12143
      · exact prime_sixtyOneBG_2210347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53680487243) ^ 26840243621 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53680487243) ^ 4420694 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53680487243) ^ 24286 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_56983897363 : Nat.Prime 56983897363 := by
  apply lucas_primality 56983897363 (2 : ZMod 56983897363)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (46784809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (46784809, 1)] : List FactorBlock).map factorBlockValue).prod) = 56983897363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_46784809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56983897363) ^ 28491948681 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56983897363) ^ 18994632454 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56983897363) ^ 8140556766 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56983897363) ^ 1964961978 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56983897363) ^ 1218 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_62910668461 : Nat.Prime 62910668461 := by
  apply lucas_primality 62910668461 (2 : ZMod 62910668461)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (383, 1), (401, 1), (6827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (383, 1), (401, 1), (6827, 1)] : List FactorBlock).map factorBlockValue).prod) = 62910668461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_383
      · exact prime_sixtyOneBG_401
      · exact prime_sixtyOneBG_6827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62910668461) ^ 31455334230 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 62910668461) ^ 20970222820 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 62910668461) ^ 12582133692 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 62910668461) ^ 164257620 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 62910668461) ^ 156884460 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 62910668461) ^ 9214980 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_72724880381 : Nat.Prime 72724880381 := by
  apply lucas_primality 72724880381 (3 : ZMod 72724880381)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (389, 1), (549863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (389, 1), (549863, 1)] : List FactorBlock).map factorBlockValue).prod) = 72724880381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_389
      · exact prime_sixtyOneBG_549863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72724880381) ^ 36362440190 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72724880381) ^ 14544976076 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72724880381) ^ 4277934140 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72724880381) ^ 186953420 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72724880381) ^ 132260 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_74719794841 : Nat.Prime 74719794841 := by
  apply lucas_primality 74719794841 (19 : ZMod 74719794841)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (622664957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (622664957, 1)] : List FactorBlock).map factorBlockValue).prod) = 74719794841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_622664957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 74719794841) ^ 37359897420 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 74719794841) ^ 24906598280 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 74719794841) ^ 14943958968 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 74719794841) ^ 120 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_90450015049 : Nat.Prime 90450015049 := by
  apply lucas_primality 90450015049 (59 : ZMod 90450015049)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (30640249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (30640249, 1)] : List FactorBlock).map factorBlockValue).prod) = 90450015049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_30640249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (59 : ZMod 90450015049) ^ 45225007524 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (59 : ZMod 90450015049) ^ 30150005016 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (59 : ZMod 90450015049) ^ 2206097928 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (59 : ZMod 90450015049) ^ 2952 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_99067423577 : Nat.Prime 99067423577 := by
  apply lucas_primality 99067423577 (3 : ZMod 99067423577)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1125766177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1125766177, 1)] : List FactorBlock).map factorBlockValue).prod) = 99067423577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_1125766177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 99067423577) ^ 49533711788 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 99067423577) ^ 9006129416 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 99067423577) ^ 88 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_99669893077 : Nat.Prime 99669893077 := by
  apply lucas_primality 99669893077 (2 : ZMod 99669893077)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (23, 1), (113, 1), (81943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (23, 1), (113, 1), (81943, 1)] : List FactorBlock).map factorBlockValue).prod) = 99669893077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_113
      · exact prime_sixtyOneBG_81943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 99669893077) ^ 49834946538 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 99669893077) ^ 33223297692 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 99669893077) ^ 7666914852 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 99669893077) ^ 4333473612 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 99669893077) ^ 882034452 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 99669893077) ^ 1216332 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_105960180173 : Nat.Prime 105960180173 := by
  apply lucas_primality 105960180173 (2 : ZMod 105960180173)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (19, 1), (18106661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (19, 1), (18106661, 1)] : List FactorBlock).map factorBlockValue).prod) = 105960180173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_18106661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105960180173) ^ 52980090086 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 105960180173) ^ 15137168596 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 105960180173) ^ 9632743652 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 105960180173) ^ 5576851588 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 105960180173) ^ 5852 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_129057477727 : Nat.Prime 129057477727 := by
  apply lucas_primality 129057477727 (3 : ZMod 129057477727)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21509579621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21509579621, 1)] : List FactorBlock).map factorBlockValue).prod) = 129057477727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_21509579621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 129057477727) ^ 64528738863 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 129057477727) ^ 43019159242 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 129057477727) ^ 6 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_129258450809 : Nat.Prime 129258450809 := by
  apply lucas_primality 129258450809 (3 : ZMod 129258450809)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (16157306351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (16157306351, 1)] : List FactorBlock).map factorBlockValue).prod) = 129258450809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_16157306351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 129258450809) ^ 64629225404 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 129258450809) ^ 8 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_150041274043 : Nat.Prime 150041274043 := by
  apply lucas_primality 150041274043 (2 : ZMod 150041274043)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 2), (4297453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 2), (4297453, 1)] : List FactorBlock).map factorBlockValue).prod) = 150041274043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_4297453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 150041274043) ^ 75020637021 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 150041274043) ^ 50013758014 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 150041274043) ^ 13640115822 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 150041274043) ^ 6523533654 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 150041274043) ^ 34914 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_241230345091 : Nat.Prime 241230345091 := by
  apply lucas_primality 241230345091 (2 : ZMod 241230345091)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1459, 1), (787331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1459, 1), (787331, 1)] : List FactorBlock).map factorBlockValue).prod) = 241230345091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_1459
      · exact prime_sixtyOneBG_787331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 241230345091) ^ 120615172545 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 241230345091) ^ 80410115030 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 241230345091) ^ 48246069018 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 241230345091) ^ 34461477870 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 241230345091) ^ 165339510 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 241230345091) ^ 306390 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_284495679049 : Nat.Prime 284495679049 := by
  apply lucas_primality 284495679049 (22 : ZMod 284495679049)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (19, 1), (5242807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (19, 1), (5242807, 1)] : List FactorBlock).map factorBlockValue).prod) = 284495679049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_5242807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 284495679049) ^ 142247839524 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (22 : ZMod 284495679049) ^ 94831893016 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (22 : ZMod 284495679049) ^ 40642239864 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (22 : ZMod 284495679049) ^ 16735039944 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (22 : ZMod 284495679049) ^ 14973456792 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (22 : ZMod 284495679049) ^ 54264 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_311766662483 : Nat.Prime 311766662483 := by
  apply lucas_primality 311766662483 (2 : ZMod 311766662483)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (107, 1), (132441233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (107, 1), (132441233, 1)] : List FactorBlock).map factorBlockValue).prod) = 311766662483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_107
      · exact prime_sixtyOneBG_132441233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 311766662483) ^ 155883331241 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 311766662483) ^ 28342423862 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 311766662483) ^ 2913707126 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 311766662483) ^ 2354 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_382571426953 : Nat.Prime 382571426953 := by
  apply lucas_primality 382571426953 (19 : ZMod 382571426953)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (13, 1), (37, 1), (251, 1), (4001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (13, 1), (37, 1), (251, 1), (4001, 1)] : List FactorBlock).map factorBlockValue).prod) = 382571426953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_37
      · exact prime_sixtyOneBG_251
      · exact prime_sixtyOneBG_4001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 382571426953) ^ 191285713476 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 382571426953) ^ 127523808984 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 382571426953) ^ 34779220632 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 382571426953) ^ 29428571304 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 382571426953) ^ 10339768296 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 382571426953) ^ 1524188952 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (19 : ZMod 382571426953) ^ 95618952 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_466774573049 : Nat.Prime 466774573049 := by
  apply lucas_primality 466774573049 (3 : ZMod 466774573049)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (53, 1), (211, 1), (39229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (53, 1), (211, 1), (39229, 1)] : List FactorBlock).map factorBlockValue).prod) = 466774573049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_53
      · exact prime_sixtyOneBG_211
      · exact prime_sixtyOneBG_39229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 466774573049) ^ 233387286524 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 466774573049) ^ 66682081864 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 466774573049) ^ 24567082792 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 466774573049) ^ 8807067416 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 466774573049) ^ 2212201768 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 466774573049) ^ 11898712 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_558348284261 : Nat.Prime 558348284261 := by
  apply lucas_primality 558348284261 (2 : ZMod 558348284261)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (43, 1), (241, 1), (207227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (43, 1), (241, 1), (207227, 1)] : List FactorBlock).map factorBlockValue).prod) = 558348284261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_43
      · exact prime_sixtyOneBG_241
      · exact prime_sixtyOneBG_207227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 558348284261) ^ 279174142130 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 558348284261) ^ 111669656852 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 558348284261) ^ 42949868020 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 558348284261) ^ 12984843820 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 558348284261) ^ 2316797860 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 558348284261) ^ 2694380 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_573717519971 : Nat.Prime 573717519971 := by
  apply lucas_primality 573717519971 (6 : ZMod 573717519971)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 2), (307, 1), (92377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 2), (307, 1), (92377, 1)] : List FactorBlock).map factorBlockValue).prod) = 573717519971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_307
      · exact prime_sixtyOneBG_92377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 573717519971) ^ 286858759985 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 573717519971) ^ 114743503994 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 573717519971) ^ 81959645710 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 573717519971) ^ 33748089410 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 573717519971) ^ 1868786710 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 573717519971) ^ 6210610 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_674210999003 : Nat.Prime 674210999003 := by
  apply lucas_primality 674210999003 (2 : ZMod 674210999003)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (69593, 1), (167033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (69593, 1), (167033, 1)] : List FactorBlock).map factorBlockValue).prod) = 674210999003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_69593
      · exact prime_sixtyOneBG_167033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 674210999003) ^ 337105499501 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674210999003) ^ 23248655138 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674210999003) ^ 9687914 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674210999003) ^ 4036394 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_774344866363 : Nat.Prime 774344866363 := by
  apply lucas_primality 774344866363 (2 : ZMod 774344866363)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (129057477727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (129057477727, 1)] : List FactorBlock).map factorBlockValue).prod) = 774344866363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_129057477727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 774344866363) ^ 387172433181 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 774344866363) ^ 258114955454 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 774344866363) ^ 6 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_801378110333 : Nat.Prime 801378110333 := by
  apply lucas_primality 801378110333 (2 : ZMod 801378110333)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (1213, 1), (912511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (1213, 1), (912511, 1)] : List FactorBlock).map factorBlockValue).prod) = 801378110333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_181
      · exact prime_sixtyOneBG_1213
      · exact prime_sixtyOneBG_912511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 801378110333) ^ 400689055166 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 801378110333) ^ 4427503372 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 801378110333) ^ 660657964 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 801378110333) ^ 878212 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_811828231153 : Nat.Prime 811828231153 := by
  apply lucas_primality 811828231153 (5 : ZMod 811828231153)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (59, 1), (241, 1), (1189471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (59, 1), (241, 1), (1189471, 1)] : List FactorBlock).map factorBlockValue).prod) = 811828231153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_59
      · exact prime_sixtyOneBG_241
      · exact prime_sixtyOneBG_1189471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 811828231153) ^ 405914115576 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 811828231153) ^ 270609410384 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 811828231153) ^ 13759800528 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 811828231153) ^ 3368581872 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 811828231153) ^ 682512 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_847629362743 : Nat.Prime 847629362743 := by
  apply lucas_primality 847629362743 (5 : ZMod 847629362743)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1033, 1), (5946023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1033, 1), (5946023, 1)] : List FactorBlock).map factorBlockValue).prod) = 847629362743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_1033
      · exact prime_sixtyOneBG_5946023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 847629362743) ^ 423814681371 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 847629362743) ^ 282543120914 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 847629362743) ^ 36853450554 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 847629362743) ^ 820551174 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 847629362743) ^ 142554 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_904673937047 : Nat.Prime 904673937047 := by
  apply lucas_primality 904673937047 (5 : ZMod 904673937047)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3361, 1), (12234913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3361, 1), (12234913, 1)] : List FactorBlock).map factorBlockValue).prod) = 904673937047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_3361
      · exact prime_sixtyOneBG_12234913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 904673937047) ^ 452336968523 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 904673937047) ^ 82243085186 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 904673937047) ^ 269168086 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 904673937047) ^ 73942 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_947487480701 : Nat.Prime 947487480701 := by
  apply lucas_primality 947487480701 (2 : ZMod 947487480701)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (47, 1), (201593081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (47, 1), (201593081, 1)] : List FactorBlock).map factorBlockValue).prod) = 947487480701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_47
      · exact prime_sixtyOneBG_201593081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 947487480701) ^ 473743740350 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 947487480701) ^ 189497496140 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 947487480701) ^ 20159308100 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 947487480701) ^ 4700 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1013728210559 : Nat.Prime 1013728210559 := by
  apply lucas_primality 1013728210559 (7 : ZMod 1013728210559)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (151, 1), (15468737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (151, 1), (15468737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013728210559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_31
      · exact prime_sixtyOneBG_151
      · exact prime_sixtyOneBG_15468737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1013728210559) ^ 506864105279 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1013728210559) ^ 144818315794 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1013728210559) ^ 32700910018 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1013728210559) ^ 6713431858 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1013728210559) ^ 65534 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1095396218041 : Nat.Prime 1095396218041 := by
  apply lucas_primality 1095396218041 (7 : ZMod 1095396218041)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (69233, 1), (131849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (69233, 1), (131849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1095396218041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_69233
      · exact prime_sixtyOneBG_131849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1095396218041) ^ 547698109020 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1095396218041) ^ 365132072680 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1095396218041) ^ 219079243608 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1095396218041) ^ 15821880 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1095396218041) ^ 8307960 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1127640650501 : Nat.Prime 1127640650501 := by
  apply lucas_primality 1127640650501 (2 : ZMod 1127640650501)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (7, 2), (13, 1), (41, 1), (86353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (7, 2), (13, 1), (41, 1), (86353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1127640650501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_86353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1127640650501) ^ 563820325250 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127640650501) ^ 225528130100 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127640650501) ^ 161091521500 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127640650501) ^ 86741588500 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127640650501) ^ 27503430500 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127640650501) ^ 13058500 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1376911011911 : Nat.Prime 1376911011911 := by
  apply lucas_primality 1376911011911 (21 : ZMod 1376911011911)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (179, 1), (4777789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (179, 1), (4777789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1376911011911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_179
      · exact prime_sixtyOneBG_4777789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 1376911011911) ^ 688455505955 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (21 : ZMod 1376911011911) ^ 275382202382 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (21 : ZMod 1376911011911) ^ 196701573130 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (21 : ZMod 1376911011911) ^ 59865696170 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (21 : ZMod 1376911011911) ^ 7692240290 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (21 : ZMod 1376911011911) ^ 288190 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1433068976011 : Nat.Prime 1433068976011 := by
  apply lucas_primality 1433068976011 (2 : ZMod 1433068976011)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (82279, 1), (82939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (82279, 1), (82939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1433068976011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_82279
      · exact prime_sixtyOneBG_82939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1433068976011) ^ 716534488005 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433068976011) ^ 477689658670 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433068976011) ^ 286613795202 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433068976011) ^ 204724139430 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433068976011) ^ 17417190 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433068976011) ^ 17278590 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1716310382939 : Nat.Prime 1716310382939 := by
  apply lucas_primality 1716310382939 (2 : ZMod 1716310382939)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1657, 1), (517896917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1657, 1), (517896917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1716310382939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_1657
      · exact prime_sixtyOneBG_517896917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1716310382939) ^ 858155191469 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716310382939) ^ 1035793834 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1716310382939) ^ 3314 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1818191891099 : Nat.Prime 1818191891099 := by
  apply lucas_primality 1818191891099 (2 : ZMod 1818191891099)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1559, 1), (53011601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1559, 1), (53011601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1818191891099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_1559
      · exact prime_sixtyOneBG_53011601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1818191891099) ^ 909095945549 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1818191891099) ^ 165290171918 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1818191891099) ^ 1166255222 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1818191891099) ^ 34298 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2747974094137 : Nat.Prime 2747974094137 := by
  apply lucas_primality 2747974094137 (7 : ZMod 2747974094137)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (29, 1), (59, 1), (3001, 1), (7433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (29, 1), (59, 1), (3001, 1), (7433, 1)] : List FactorBlock).map factorBlockValue).prod) = 2747974094137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_59
      · exact prime_sixtyOneBG_3001
      · exact prime_sixtyOneBG_7433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2747974094137) ^ 1373987047068 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2747974094137) ^ 915991364712 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2747974094137) ^ 94757727384 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2747974094137) ^ 46575832104 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2747974094137) ^ 915686136 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2747974094137) ^ 369699192 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3598709997979 : Nat.Prime 3598709997979 := by
  apply lucas_primality 3598709997979 (3 : ZMod 3598709997979)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (647, 1), (13435141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (647, 1), (13435141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3598709997979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_647
      · exact prime_sixtyOneBG_13435141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3598709997979) ^ 1799354998989 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3598709997979) ^ 1199569999326 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3598709997979) ^ 156465652086 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3598709997979) ^ 5562148374 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3598709997979) ^ 267858 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_4239088085179 : Nat.Prime 4239088085179 := by
  apply lucas_primality 4239088085179 (2 : ZMod 4239088085179)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (61, 1), (229, 1), (5619703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (61, 1), (229, 1), (5619703, 1)] : List FactorBlock).map factorBlockValue).prod) = 4239088085179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_61
      · exact prime_sixtyOneBG_229
      · exact prime_sixtyOneBG_5619703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4239088085179) ^ 2119544042589 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4239088085179) ^ 1413029361726 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4239088085179) ^ 69493247298 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4239088085179) ^ 18511301682 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4239088085179) ^ 754326 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_4478092795277 : Nat.Prime 4478092795277 := by
  apply lucas_primality 4478092795277 (2 : ZMod 4478092795277)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (21123079223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (21123079223, 1)] : List FactorBlock).map factorBlockValue).prod) = 4478092795277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_53
      · exact prime_sixtyOneBG_21123079223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4478092795277) ^ 2239046397638 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4478092795277) ^ 84492316892 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4478092795277) ^ 212 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_5379825228553 : Nat.Prime 5379825228553 := by
  apply lucas_primality 5379825228553 (5 : ZMod 5379825228553)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (74719794841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (74719794841, 1)] : List FactorBlock).map factorBlockValue).prod) = 5379825228553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_74719794841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5379825228553) ^ 2689912614276 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5379825228553) ^ 1793275076184 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5379825228553) ^ 72 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_6337336267579 : Nat.Prime 6337336267579 := by
  apply lucas_primality 6337336267579 (10 : ZMod 6337336267579)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (6917, 1), (3724379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (6917, 1), (3724379, 1)] : List FactorBlock).map factorBlockValue).prod) = 6337336267579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_6917
      · exact prime_sixtyOneBG_3724379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6337336267579) ^ 3168668133789 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 6337336267579) ^ 2112445422526 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 6337336267579) ^ 154569177258 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 6337336267579) ^ 916197234 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (10 : ZMod 6337336267579) ^ 1701582 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_9130675655729 : Nat.Prime 9130675655729 := by
  apply lucas_primality 9130675655729 (3 : ZMod 9130675655729)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (17, 1), (743, 1), (4107263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (17, 1), (743, 1), (4107263, 1)] : List FactorBlock).map factorBlockValue).prod) = 9130675655729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_743
      · exact prime_sixtyOneBG_4107263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9130675655729) ^ 4565337827864 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9130675655729) ^ 830061423248 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9130675655729) ^ 537098567984 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9130675655729) ^ 12288930896 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9130675655729) ^ 2223056 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_9649213803641 : Nat.Prime 9649213803641 := by
  apply lucas_primality 9649213803641 (3 : ZMod 9649213803641)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (241230345091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (241230345091, 1)] : List FactorBlock).map factorBlockValue).prod) = 9649213803641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_241230345091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9649213803641) ^ 4824606901820 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9649213803641) ^ 1929842760728 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9649213803641) ^ 40 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_10624814515859 : Nat.Prime 10624814515859 := by
  apply lucas_primality 10624814515859 (2 : ZMod 10624814515859)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8123, 1), (653995723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8123, 1), (653995723, 1)] : List FactorBlock).map factorBlockValue).prod) = 10624814515859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_8123
      · exact prime_sixtyOneBG_653995723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10624814515859) ^ 5312407257929 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10624814515859) ^ 1307991446 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10624814515859) ^ 16246 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_11854066927933 : Nat.Prime 11854066927933 := by
  apply lucas_primality 11854066927933 (5 : ZMod 11854066927933)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (10273, 1), (681977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (10273, 1), (681977, 1)] : List FactorBlock).map factorBlockValue).prod) = 11854066927933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_47
      · exact prime_sixtyOneBG_10273
      · exact prime_sixtyOneBG_681977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11854066927933) ^ 5927033463966 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11854066927933) ^ 3951355642644 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11854066927933) ^ 252214189956 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11854066927933) ^ 1153905084 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11854066927933) ^ 17381916 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_14019009516341 : Nat.Prime 14019009516341 := by
  apply lucas_primality 14019009516341 (2 : ZMod 14019009516341)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (457, 1), (1021, 1), (31963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (457, 1), (1021, 1), (31963, 1)] : List FactorBlock).map factorBlockValue).prod) = 14019009516341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_47
      · exact prime_sixtyOneBG_457
      · exact prime_sixtyOneBG_1021
      · exact prime_sixtyOneBG_31963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14019009516341) ^ 7009504758170 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14019009516341) ^ 2803801903268 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14019009516341) ^ 298276798220 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14019009516341) ^ 30676169620 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14019009516341) ^ 13730665540 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14019009516341) ^ 438601180 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_14029974650057 : Nat.Prime 14029974650057 := by
  apply lucas_primality 14029974650057 (3 : ZMod 14029974650057)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (137, 1), (673740619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (137, 1), (673740619, 1)] : List FactorBlock).map factorBlockValue).prod) = 14029974650057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_137
      · exact prime_sixtyOneBG_673740619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14029974650057) ^ 7014987325028 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14029974650057) ^ 738419718424 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14029974650057) ^ 102408574088 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14029974650057) ^ 20824 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_14573992814611 : Nat.Prime 14573992814611 := by
  apply lucas_primality 14573992814611 (3 : ZMod 14573992814611)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (103, 1), (4716502529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (103, 1), (4716502529, 1)] : List FactorBlock).map factorBlockValue).prod) = 14573992814611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_103
      · exact prime_sixtyOneBG_4716502529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14573992814611) ^ 7286996407305 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14573992814611) ^ 4857997604870 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14573992814611) ^ 2914798562922 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14573992814611) ^ 141495075870 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14573992814611) ^ 3090 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_17211525599131 : Nat.Prime 17211525599131 := by
  apply lucas_primality 17211525599131 (2 : ZMod 17211525599131)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (573717519971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (573717519971, 1)] : List FactorBlock).map factorBlockValue).prod) = 17211525599131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_573717519971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17211525599131) ^ 8605762799565 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17211525599131) ^ 5737175199710 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17211525599131) ^ 3442305119826 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17211525599131) ^ 30 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_20236533621649 : Nat.Prime 20236533621649 := by
  apply lucas_primality 20236533621649 (26 : ZMod 20236533621649)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1301, 1), (324054151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1301, 1), (324054151, 1)] : List FactorBlock).map factorBlockValue).prod) = 20236533621649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_1301
      · exact prime_sixtyOneBG_324054151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 20236533621649) ^ 10118266810824 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (26 : ZMod 20236533621649) ^ 6745511207216 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (26 : ZMod 20236533621649) ^ 15554599248 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (26 : ZMod 20236533621649) ^ 62448 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_21519300914213 : Nat.Prime 21519300914213 := by
  apply lucas_primality 21519300914213 (2 : ZMod 21519300914213)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5379825228553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5379825228553, 1)] : List FactorBlock).map factorBlockValue).prod) = 21519300914213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5379825228553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 21519300914213) ^ 10759650457106 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21519300914213) ^ 4 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_26840072291141 : Nat.Prime 26840072291141 := by
  apply lucas_primality 26840072291141 (2 : ZMod 26840072291141)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (41, 1), (139, 1), (6364339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (41, 1), (139, 1), (6364339, 1)] : List FactorBlock).map factorBlockValue).prod) = 26840072291141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_37
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_139
      · exact prime_sixtyOneBG_6364339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26840072291141) ^ 13420036145570 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26840072291141) ^ 5368014458228 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26840072291141) ^ 725407359220 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26840072291141) ^ 654635909540 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26840072291141) ^ 193094045260 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 26840072291141) ^ 4217260 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_31781513998357 : Nat.Prime 31781513998357 := by
  apply lucas_primality 31781513998357 (2 : ZMod 31781513998357)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1697, 1), (1560671479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1697, 1), (1560671479, 1)] : List FactorBlock).map factorBlockValue).prod) = 31781513998357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_1697
      · exact prime_sixtyOneBG_1560671479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31781513998357) ^ 15890756999178 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31781513998357) ^ 10593837999452 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31781513998357) ^ 18728057748 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31781513998357) ^ 20364 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_47416267711733 : Nat.Prime 47416267711733 := by
  apply lucas_primality 47416267711733 (2 : ZMod 47416267711733)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11854066927933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11854066927933, 1)] : List FactorBlock).map factorBlockValue).prod) = 47416267711733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11854066927933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 47416267711733) ^ 23708133855866 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47416267711733) ^ 4 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_60022152659533 : Nat.Prime 60022152659533 := by
  apply lucas_primality 60022152659533 (2 : ZMod 60022152659533)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (59, 1), (151, 1), (3487189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (59, 1), (151, 1), (3487189, 1)] : List FactorBlock).map factorBlockValue).prod) = 60022152659533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_59
      · exact prime_sixtyOneBG_151
      · exact prime_sixtyOneBG_3487189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60022152659533) ^ 30011076329766 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 60022152659533) ^ 20007384219844 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 60022152659533) ^ 8574593237076 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 60022152659533) ^ 2609658811284 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 60022152659533) ^ 1017324621348 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 60022152659533) ^ 397497699732 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 60022152659533) ^ 17212188 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_83274080731489 : Nat.Prime 83274080731489 := by
  apply lucas_primality 83274080731489 (11 : ZMod 83274080731489)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (109, 1), (6373, 1), (416243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (109, 1), (6373, 1), (416243, 1)] : List FactorBlock).map factorBlockValue).prod) = 83274080731489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_109
      · exact prime_sixtyOneBG_6373
      · exact prime_sixtyOneBG_416243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 83274080731489) ^ 41637040365744 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 83274080731489) ^ 27758026910496 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 83274080731489) ^ 763982392032 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 83274080731489) ^ 13066700256 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 83274080731489) ^ 200061216 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_84998516126873 : Nat.Prime 84998516126873 := by
  apply lucas_primality 84998516126873 (3 : ZMod 84998516126873)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10624814515859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10624814515859, 1)] : List FactorBlock).map factorBlockValue).prod) = 84998516126873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_10624814515859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 84998516126873) ^ 42499258063436 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 84998516126873) ^ 8 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_154811252349961 : Nat.Prime 154811252349961 := by
  apply lucas_primality 154811252349961 (62 : ZMod 154811252349961)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (14293, 1), (5309443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (14293, 1), (5309443, 1)] : List FactorBlock).map factorBlockValue).prod) = 154811252349961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_14293
      · exact prime_sixtyOneBG_5309443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (62 : ZMod 154811252349961) ^ 77405626174980 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (62 : ZMod 154811252349961) ^ 51603750783320 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (62 : ZMod 154811252349961) ^ 30962250469992 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (62 : ZMod 154811252349961) ^ 9106544255880 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (62 : ZMod 154811252349961) ^ 10831263720 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (62 : ZMod 154811252349961) ^ 29157720 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_165826473217481 : Nat.Prime 165826473217481 := by
  apply lucas_primality 165826473217481 (7 : ZMod 165826473217481)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (70321, 1), (583697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (70321, 1), (583697, 1)] : List FactorBlock).map factorBlockValue).prod) = 165826473217481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_101
      · exact prime_sixtyOneBG_70321
      · exact prime_sixtyOneBG_583697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 165826473217481) ^ 82913236608740 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 165826473217481) ^ 33165294643496 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 165826473217481) ^ 1641846269480 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 165826473217481) ^ 2358135880 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 165826473217481) ^ 284096840 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_172115255991311 : Nat.Prime 172115255991311 := by
  apply lucas_primality 172115255991311 (17 : ZMod 172115255991311)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17211525599131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17211525599131, 1)] : List FactorBlock).map factorBlockValue).prod) = 172115255991311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_17211525599131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 172115255991311) ^ 86057627995655 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (17 : ZMod 172115255991311) ^ 34423051198262 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (17 : ZMod 172115255991311) ^ 10 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_200867345908613 : Nat.Prime 200867345908613 := by
  apply lucas_primality 200867345908613 (2 : ZMod 200867345908613)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (947487480701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (947487480701, 1)] : List FactorBlock).map factorBlockValue).prod) = 200867345908613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_53
      · exact prime_sixtyOneBG_947487480701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 200867345908613) ^ 100433672954306 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 200867345908613) ^ 3789949922804 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 200867345908613) ^ 212 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_227758726451941 : Nat.Prime 227758726451941 := by
  apply lucas_primality 227758726451941 (2 : ZMod 227758726451941)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (116731, 1), (32519029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (116731, 1), (32519029, 1)] : List FactorBlock).map factorBlockValue).prod) = 227758726451941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_116731
      · exact prime_sixtyOneBG_32519029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 227758726451941) ^ 113879363225970 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 227758726451941) ^ 75919575483980 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 227758726451941) ^ 45551745290388 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 227758726451941) ^ 1951141740 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 227758726451941) ^ 7003860 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_261972064479079 : Nat.Prime 261972064479079 := by
  apply lucas_primality 261972064479079 (6 : ZMod 261972064479079)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (97, 1), (150041274043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (97, 1), (150041274043, 1)] : List FactorBlock).map factorBlockValue).prod) = 261972064479079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_97
      · exact prime_sixtyOneBG_150041274043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 261972064479079) ^ 130986032239539 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 261972064479079) ^ 87324021493026 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 261972064479079) ^ 2700742932774 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 261972064479079) ^ 1746 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_306648761420663 : Nat.Prime 306648761420663 := by
  apply lucas_primality 306648761420663 (5 : ZMod 306648761420663)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1447, 1), (105960180173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1447, 1), (105960180173, 1)] : List FactorBlock).map factorBlockValue).prod) = 306648761420663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_1447
      · exact prime_sixtyOneBG_105960180173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 306648761420663) ^ 153324380710331 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 306648761420663) ^ 211920360346 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 306648761420663) ^ 2894 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_355190689847659 : Nat.Prime 355190689847659 := by
  apply lucas_primality 355190689847659 (2 : ZMod 355190689847659)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (338119, 1), (25011671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (338119, 1), (25011671, 1)] : List FactorBlock).map factorBlockValue).prod) = 355190689847659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_338119
      · exact prime_sixtyOneBG_25011671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355190689847659) ^ 177595344923829 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 355190689847659) ^ 118396896615886 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 355190689847659) ^ 50741527121094 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 355190689847659) ^ 1050490182 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 355190689847659) ^ 14200998 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_417569335188191 : Nat.Prime 417569335188191 := by
  apply lucas_primality 417569335188191 (7 : ZMod 417569335188191)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79843, 1), (522988033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79843, 1), (522988033, 1)] : List FactorBlock).map factorBlockValue).prod) = 417569335188191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_79843
      · exact prime_sixtyOneBG_522988033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 417569335188191) ^ 208784667594095 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 417569335188191) ^ 83513867037638 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 417569335188191) ^ 5229880330 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 417569335188191) ^ 798430 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_446327681339987 : Nat.Prime 446327681339987 := by
  apply lucas_primality 446327681339987 (2 : ZMod 446327681339987)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (674210999003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (674210999003, 1)] : List FactorBlock).map factorBlockValue).prod) = 446327681339987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_331
      · exact prime_sixtyOneBG_674210999003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 446327681339987) ^ 223163840669993 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 446327681339987) ^ 1348421998006 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 446327681339987) ^ 662 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_730320038062327 : Nat.Prime 730320038062327 := by
  apply lucas_primality 730320038062327 (3 : ZMod 730320038062327)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (61, 1), (277, 1), (593, 1), (94169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (61, 1), (277, 1), (593, 1), (94169, 1)] : List FactorBlock).map factorBlockValue).prod) = 730320038062327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_43
      · exact prime_sixtyOneBG_61
      · exact prime_sixtyOneBG_277
      · exact prime_sixtyOneBG_593
      · exact prime_sixtyOneBG_94169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 730320038062327) ^ 365160019031163 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 730320038062327) ^ 243440012687442 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 730320038062327) ^ 16984186931682 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 730320038062327) ^ 11972459640366 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 730320038062327) ^ 2636534433438 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 730320038062327) ^ 1231568360982 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 730320038062327) ^ 7755418854 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1048900954470931 : Nat.Prime 1048900954470931 := by
  apply lucas_primality 1048900954470931 (3 : ZMod 1048900954470931)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (271, 1), (3909579017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (271, 1), (3909579017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1048900954470931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_271
      · exact prime_sixtyOneBG_3909579017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1048900954470931) ^ 524450477235465 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1048900954470931) ^ 349633651490310 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1048900954470931) ^ 209780190894186 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1048900954470931) ^ 95354632224630 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1048900954470931) ^ 3870483226830 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1048900954470931) ^ 268290 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1070781868981807 : Nat.Prime 1070781868981807 := by
  apply lucas_primality 1070781868981807 (3 : ZMod 1070781868981807)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (836071, 1), (213455131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (836071, 1), (213455131, 1)] : List FactorBlock).map factorBlockValue).prod) = 1070781868981807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_836071
      · exact prime_sixtyOneBG_213455131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1070781868981807) ^ 535390934490903 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070781868981807) ^ 356927289660602 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070781868981807) ^ 1280730786 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070781868981807) ^ 5016426 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1096049181006491 : Nat.Prime 1096049181006491 := by
  apply lucas_primality 1096049181006491 (2 : ZMod 1096049181006491)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (241, 1), (617, 1), (737102417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (241, 1), (617, 1), (737102417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1096049181006491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_241
      · exact prime_sixtyOneBG_617
      · exact prime_sixtyOneBG_737102417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1096049181006491) ^ 548024590503245 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096049181006491) ^ 219209836201298 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096049181006491) ^ 4547921912890 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096049181006491) ^ 1776416824970 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096049181006491) ^ 1486970 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1176923213049863 : Nat.Prime 1176923213049863 := by
  apply lucas_primality 1176923213049863 (5 : ZMod 1176923213049863)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (993781, 1), (592144151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (993781, 1), (592144151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1176923213049863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_993781
      · exact prime_sixtyOneBG_592144151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1176923213049863) ^ 588461606524931 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1176923213049863) ^ 1184288302 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1176923213049863) ^ 1987562 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1576240967865133 : Nat.Prime 1576240967865133 := by
  apply lucas_primality 1576240967865133 (5 : ZMod 1576240967865133)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (157, 2), (65789569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (157, 2), (65789569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576240967865133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_157
      · exact prime_sixtyOneBG_65789569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1576240967865133) ^ 788120483932566 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1576240967865133) ^ 525413655955044 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1576240967865133) ^ 10039751387676 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1576240967865133) ^ 23958828 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2131833987427073 : Nat.Prime 2131833987427073 := by
  apply lucas_primality 2131833987427073 (3 : ZMod 2131833987427073)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (17, 1), (71, 1), (1459, 1), (4728799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (17, 1), (71, 1), (1459, 1), (4728799, 1)] : List FactorBlock).map factorBlockValue).prod) = 2131833987427073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_71
      · exact prime_sixtyOneBG_1459
      · exact prime_sixtyOneBG_4728799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2131833987427073) ^ 1065916993713536 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2131833987427073) ^ 125401999260416 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2131833987427073) ^ 30025830808832 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2131833987427073) ^ 1461161060608 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2131833987427073) ^ 450819328 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2233069998008951 : Nat.Prime 2233069998008951 := by
  apply lucas_primality 2233069998008951 (29 : ZMod 2233069998008951)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (59, 1), (613, 1), (1234866037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (59, 1), (613, 1), (1234866037, 1)] : List FactorBlock).map factorBlockValue).prod) = 2233069998008951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_59
      · exact prime_sixtyOneBG_613
      · exact prime_sixtyOneBG_1234866037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 2233069998008951) ^ 1116534999004475 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (29 : ZMod 2233069998008951) ^ 446613999601790 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (29 : ZMod 2233069998008951) ^ 37848644034050 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (29 : ZMod 2233069998008951) ^ 3642854809150 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (29 : ZMod 2233069998008951) ^ 1808350 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3950306879936377 : Nat.Prime 3950306879936377 := by
  apply lucas_primality 3950306879936377 (5 : ZMod 3950306879936377)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (23, 1), (31, 1), (163, 1), (7829, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (23, 1), (31, 1), (163, 1), (7829, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod) = 3950306879936377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_31
      · exact prime_sixtyOneBG_163
      · exact prime_sixtyOneBG_7829
      · exact prime_sixtyOneBG_9521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3950306879936377) ^ 1975153439968188 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950306879936377) ^ 1316768959978792 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950306879936377) ^ 207910888417704 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950306879936377) ^ 171752473040712 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950306879936377) ^ 127429254191496 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950306879936377) ^ 24235011533352 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950306879936377) ^ 504573621144 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950306879936377) ^ 414904619256 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3987200381088011 : Nat.Prime 3987200381088011 := by
  apply lucas_primality 3987200381088011 (2 : ZMod 3987200381088011)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (71, 1), (57773, 1), (5717891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (71, 1), (57773, 1), (5717891, 1)] : List FactorBlock).map factorBlockValue).prod) = 3987200381088011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_71
      · exact prime_sixtyOneBG_57773
      · exact prime_sixtyOneBG_5717891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3987200381088011) ^ 1993600190544005 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3987200381088011) ^ 797440076217602 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3987200381088011) ^ 234541198887530 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3987200381088011) ^ 56157751846310 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3987200381088011) ^ 69014944370 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3987200381088011) ^ 697320110 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_4285808205231877 : Nat.Prime 4285808205231877 := by
  apply lucas_primality 4285808205231877 (2 : ZMod 4285808205231877)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (877, 1), (7683799483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (877, 1), (7683799483, 1)] : List FactorBlock).map factorBlockValue).prod) = 4285808205231877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_53
      · exact prime_sixtyOneBG_877
      · exact prime_sixtyOneBG_7683799483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4285808205231877) ^ 2142904102615938 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285808205231877) ^ 1428602735077292 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285808205231877) ^ 80864305759092 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285808205231877) ^ 4886896471188 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4285808205231877) ^ 557772 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_5310697517561477 : Nat.Prime 5310697517561477 := by
  apply lucas_primality 5310697517561477 (2 : ZMod 5310697517561477)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157327, 1), (8438948047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157327, 1), (8438948047, 1)] : List FactorBlock).map factorBlockValue).prod) = 5310697517561477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_157327
      · exact prime_sixtyOneBG_8438948047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5310697517561477) ^ 2655348758780738 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5310697517561477) ^ 33755792188 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5310697517561477) ^ 629308 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_7461977295622457 : Nat.Prime 7461977295622457 := by
  apply lucas_primality 7461977295622457 (3 : ZMod 7461977295622457)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (19, 1), (137, 1), (877, 1), (24034841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (19, 1), (137, 1), (877, 1), (24034841, 1)] : List FactorBlock).map factorBlockValue).prod) = 7461977295622457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_137
      · exact prime_sixtyOneBG_877
      · exact prime_sixtyOneBG_24034841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7461977295622457) ^ 3730988647811228 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7461977295622457) ^ 438939840918968 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7461977295622457) ^ 392735647138024 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7461977295622457) ^ 54466987559288 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7461977295622457) ^ 8508525992728 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7461977295622457) ^ 310465016 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_10647676509681773 : Nat.Prime 10647676509681773 := by
  apply lucas_primality 10647676509681773 (2 : ZMod 10647676509681773)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3748079, 1), (64564447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3748079, 1), (64564447, 1)] : List FactorBlock).map factorBlockValue).prod) = 10647676509681773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_3748079
      · exact prime_sixtyOneBG_64564447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10647676509681773) ^ 5323838254840886 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10647676509681773) ^ 967970591789252 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10647676509681773) ^ 2840835668 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10647676509681773) ^ 164915476 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_11221940118362203 : Nat.Prime 11221940118362203 := by
  apply lucas_primality 11221940118362203 (3 : ZMod 11221940118362203)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3547, 1), (221957, 1), (791891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3547, 1), (221957, 1), (791891, 1)] : List FactorBlock).map factorBlockValue).prod) = 11221940118362203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_3547
      · exact prime_sixtyOneBG_221957
      · exact prime_sixtyOneBG_791891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11221940118362203) ^ 5610970059181101 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11221940118362203) ^ 3740646706120734 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11221940118362203) ^ 3163783512366 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11221940118362203) ^ 50559072786 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11221940118362203) ^ 14171066622 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_14998804143424163 : Nat.Prime 14998804143424163 := by
  apply lucas_primality 14998804143424163 (2 : ZMod 14998804143424163)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (6264781, 1), (8034049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (6264781, 1), (8034049, 1)] : List FactorBlock).map factorBlockValue).prod) = 14998804143424163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_149
      · exact prime_sixtyOneBG_6264781
      · exact prime_sixtyOneBG_8034049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14998804143424163) ^ 7499402071712081 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14998804143424163) ^ 100663115056538 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14998804143424163) ^ 2394146602 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14998804143424163) ^ 1866904738 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_21136112398986811 : Nat.Prime 21136112398986811 := by
  apply lucas_primality 21136112398986811 (7 : ZMod 21136112398986811)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (257, 1), (32381, 1), (84660431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (257, 1), (32381, 1), (84660431, 1)] : List FactorBlock).map factorBlockValue).prod) = 21136112398986811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_257
      · exact prime_sixtyOneBG_32381
      · exact prime_sixtyOneBG_84660431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21136112398986811) ^ 10568056199493405 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21136112398986811) ^ 7045370799662270 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21136112398986811) ^ 4227222479797362 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21136112398986811) ^ 82241682486330 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21136112398986811) ^ 652731923010 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 21136112398986811) ^ 249657510 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_30387325065258067 : Nat.Prime 30387325065258067 := by
  apply lucas_primality 30387325065258067 (7 : ZMod 30387325065258067)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (541, 1), (1789163, 1), (5232317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (541, 1), (1789163, 1), (5232317, 1)] : List FactorBlock).map factorBlockValue).prod) = 30387325065258067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_541
      · exact prime_sixtyOneBG_1789163
      · exact prime_sixtyOneBG_5232317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 30387325065258067) ^ 15193662532629033 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30387325065258067) ^ 10129108355086022 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30387325065258067) ^ 56168807884026 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30387325065258067) ^ 16984100982 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30387325065258067) ^ 5807623098 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_32004415360578949 : Nat.Prime 32004415360578949 := by
  apply lucas_primality 32004415360578949 (2 : ZMod 32004415360578949)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (193247, 1), (1971595651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (193247, 1), (1971595651, 1)] : List FactorBlock).map factorBlockValue).prod) = 32004415360578949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_193247
      · exact prime_sixtyOneBG_1971595651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32004415360578949) ^ 16002207680289474 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 32004415360578949) ^ 10668138453526316 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 32004415360578949) ^ 4572059337225564 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 32004415360578949) ^ 165614034684 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 32004415360578949) ^ 16232748 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_38625861440561743 : Nat.Prime 38625861440561743 := by
  apply lucas_primality 38625861440561743 (6 : ZMod 38625861440561743)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (653, 1), (1095396218041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (653, 1), (1095396218041, 1)] : List FactorBlock).map factorBlockValue).prod) = 38625861440561743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_653
      · exact prime_sixtyOneBG_1095396218041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 38625861440561743) ^ 19312930720280871 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 38625861440561743) ^ 12875287146853914 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 38625861440561743) ^ 59151395774214 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 38625861440561743) ^ 35262 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_53496492916545803 : Nat.Prime 53496492916545803 := by
  apply lucas_primality 53496492916545803 (2 : ZMod 53496492916545803)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (503, 1), (382571426953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (503, 1), (382571426953, 1)] : List FactorBlock).map factorBlockValue).prod) = 53496492916545803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_139
      · exact prime_sixtyOneBG_503
      · exact prime_sixtyOneBG_382571426953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53496492916545803) ^ 26748246458272901 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53496492916545803) ^ 384866855514718 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53496492916545803) ^ 106354856692934 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53496492916545803) ^ 139834 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_58969866645947987 : Nat.Prime 58969866645947987 := by
  apply lucas_primality 58969866645947987 (2 : ZMod 58969866645947987)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (151, 1), (2027, 1), (10061, 1), (142907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (151, 1), (2027, 1), (10061, 1), (142907, 1)] : List FactorBlock).map factorBlockValue).prod) = 58969866645947987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_67
      · exact prime_sixtyOneBG_151
      · exact prime_sixtyOneBG_2027
      · exact prime_sixtyOneBG_10061
      · exact prime_sixtyOneBG_142907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58969866645947987) ^ 29484933322973993 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58969866645947987) ^ 880147263372358 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58969866645947987) ^ 390528918185086 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58969866645947987) ^ 29092188774518 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58969866645947987) ^ 5861233142426 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 58969866645947987) ^ 412645053398 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_59698290009841661 : Nat.Prime 59698290009841661 := by
  apply lucas_primality 59698290009841661 (2 : ZMod 59698290009841661)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (8052073, 1), (21805963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (8052073, 1), (21805963, 1)] : List FactorBlock).map factorBlockValue).prod) = 59698290009841661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_8052073
      · exact prime_sixtyOneBG_21805963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59698290009841661) ^ 29849145004920830 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698290009841661) ^ 11939658001968332 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698290009841661) ^ 3511664118225980 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698290009841661) ^ 7414027420 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698290009841661) ^ 2737704820 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_62792895760045681 : Nat.Prime 62792895760045681 := by
  apply lucas_primality 62792895760045681 (11 : ZMod 62792895760045681)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (139, 1), (99067423577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (139, 1), (99067423577, 1)] : List FactorBlock).map factorBlockValue).prod) = 62792895760045681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_139
      · exact prime_sixtyOneBG_99067423577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 62792895760045681) ^ 31396447880022840 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 62792895760045681) ^ 20930965253348560 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 62792895760045681) ^ 12558579152009136 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 62792895760045681) ^ 3304889250528720 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 62792895760045681) ^ 451747451511120 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 62792895760045681) ^ 633840 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_63955019622812191 : Nat.Prime 63955019622812191 := by
  apply lucas_primality 63955019622812191 (17 : ZMod 63955019622812191)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2131833987427073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2131833987427073, 1)] : List FactorBlock).map factorBlockValue).prod) = 63955019622812191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_2131833987427073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 63955019622812191) ^ 31977509811406095 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (17 : ZMod 63955019622812191) ^ 21318339874270730 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (17 : ZMod 63955019622812191) ^ 12791003924562438 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (17 : ZMod 63955019622812191) ^ 30 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_67331640710173219 : Nat.Prime 67331640710173219 := by
  apply lucas_primality 67331640710173219 (7 : ZMod 67331640710173219)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11221940118362203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11221940118362203, 1)] : List FactorBlock).map factorBlockValue).prod) = 67331640710173219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_11221940118362203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 67331640710173219) ^ 33665820355086609 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 67331640710173219) ^ 22443880236724406 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 67331640710173219) ^ 6 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_73897279339407443 : Nat.Prime 73897279339407443 := by
  apply lucas_primality 73897279339407443 (2 : ZMod 73897279339407443)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (21519300914213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (21519300914213, 1)] : List FactorBlock).map factorBlockValue).prod) = 73897279339407443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_101
      · exact prime_sixtyOneBG_21519300914213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73897279339407443) ^ 36948639669703721 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73897279339407443) ^ 4346898784671026 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73897279339407443) ^ 731656231083242 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73897279339407443) ^ 3434 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_84727531338529589 : Nat.Prime 84727531338529589 := by
  apply lucas_primality 84727531338529589 (2 : ZMod 84727531338529589)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (391889, 1), (2844774767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (391889, 1), (2844774767, 1)] : List FactorBlock).map factorBlockValue).prod) = 84727531338529589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_391889
      · exact prime_sixtyOneBG_2844774767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84727531338529589) ^ 42363765669264794 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 84727531338529589) ^ 4459343754659452 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 84727531338529589) ^ 216202882292 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 84727531338529589) ^ 29783564 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_103030379201507327 : Nat.Prime 103030379201507327 := by
  apply lucas_primality 103030379201507327 (5 : ZMod 103030379201507327)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (699187, 1), (3203421763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (699187, 1), (3203421763, 1)] : List FactorBlock).map factorBlockValue).prod) = 103030379201507327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_699187
      · exact prime_sixtyOneBG_3203421763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 103030379201507327) ^ 51515189600753663 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 103030379201507327) ^ 4479581704413362 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 103030379201507327) ^ 147357401098 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 103030379201507327) ^ 32162602 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_110608592638218557 : Nat.Prime 110608592638218557 := by
  apply lucas_primality 110608592638218557 (2 : ZMod 110608592638218557)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3950306879936377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3950306879936377, 1)] : List FactorBlock).map factorBlockValue).prod) = 110608592638218557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_3950306879936377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 110608592638218557) ^ 55304296319109278 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110608592638218557) ^ 15801227519745508 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110608592638218557) ^ 28 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_137663030342014141 : Nat.Prime 137663030342014141 := by
  apply lucas_primality 137663030342014141 (2 : ZMod 137663030342014141)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2963, 1), (774344866363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2963, 1), (774344866363, 1)] : List FactorBlock).map factorBlockValue).prod) = 137663030342014141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_2963
      · exact prime_sixtyOneBG_774344866363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137663030342014141) ^ 68831515171007070 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137663030342014141) ^ 45887676780671380 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137663030342014141) ^ 27532606068402828 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137663030342014141) ^ 46460691981780 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137663030342014141) ^ 177780 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_415276168317976963 : Nat.Prime 415276168317976963 := by
  apply lucas_primality 415276168317976963 (2 : ZMod 415276168317976963)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1231, 1), (1009807, 1), (18559577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1231, 1), (1009807, 1), (18559577, 1)] : List FactorBlock).map factorBlockValue).prod) = 415276168317976963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_1231
      · exact prime_sixtyOneBG_1009807
      · exact prime_sixtyOneBG_18559577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 415276168317976963) ^ 207638084158988481 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 415276168317976963) ^ 138425389439325654 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 415276168317976963) ^ 337348633889502 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 415276168317976963) ^ 411243107166 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 415276168317976963) ^ 22375303506 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_659675122022990221 : Nat.Prime 659675122022990221 := by
  apply lucas_primality 659675122022990221 (13 : ZMod 659675122022990221)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (97, 1), (2213, 1), (7316909231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (97, 1), (2213, 1), (7316909231, 1)] : List FactorBlock).map factorBlockValue).prod) = 659675122022990221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_97
      · exact prime_sixtyOneBG_2213
      · exact prime_sixtyOneBG_7316909231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 659675122022990221) ^ 329837561011495110 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 659675122022990221) ^ 219891707340996740 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 659675122022990221) ^ 131935024404598044 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 659675122022990221) ^ 94239303146141460 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 659675122022990221) ^ 6800774453845260 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 659675122022990221) ^ 298090882070940 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (13 : ZMod 659675122022990221) ^ 90157620 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_767482643058003361 : Nat.Prime 767482643058003361 := by
  apply lucas_primality 767482643058003361 (7 : ZMod 767482643058003361)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (8634161, 1), (61728529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (8634161, 1), (61728529, 1)] : List FactorBlock).map factorBlockValue).prod) = 767482643058003361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_8634161
      · exact prime_sixtyOneBG_61728529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 767482643058003361) ^ 383741321529001680 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 767482643058003361) ^ 255827547686001120 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 767482643058003361) ^ 153496528611600672 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 767482643058003361) ^ 88889081760 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 767482643058003361) ^ 12433191840 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_797327450871103931 : Nat.Prime 797327450871103931 := by
  apply lucas_primality 797327450871103931 (7 : ZMod 797327450871103931)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (1898629, 1), (1134997441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (1898629, 1), (1134997441, 1)] : List FactorBlock).map factorBlockValue).prod) = 797327450871103931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_37
      · exact prime_sixtyOneBG_1898629
      · exact prime_sixtyOneBG_1134997441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 797327450871103931) ^ 398663725435551965 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 797327450871103931) ^ 159465490174220786 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 797327450871103931) ^ 21549390564083890 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 797327450871103931) ^ 419949053170 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 797327450871103931) ^ 702492730 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1023366151742671309 : Nat.Prime 1023366151742671309 := by
  apply lucas_primality 1023366151742671309 (2 : ZMod 1023366151742671309)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (13, 1), (128981, 1), (420334793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (13, 1), (128981, 1), (420334793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1023366151742671309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_128981
      · exact prime_sixtyOneBG_420334793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1023366151742671309) ^ 511683075871335654 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1023366151742671309) ^ 341122050580890436 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1023366151742671309) ^ 93033286522061028 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1023366151742671309) ^ 78720473210974716 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1023366151742671309) ^ 7934239552668 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1023366151742671309) ^ 2434645356 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1599479939570178209 : Nat.Prime 1599479939570178209 := by
  apply lucas_primality 1599479939570178209 (3 : ZMod 1599479939570178209)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (163, 1), (306648761420663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (163, 1), (306648761420663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1599479939570178209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_163
      · exact prime_sixtyOneBG_306648761420663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1599479939570178209) ^ 799739969785089104 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1599479939570178209) ^ 9812760365461216 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1599479939570178209) ^ 5216 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_9001745604955853489 : Nat.Prime 9001745604955853489 := by
  apply lucas_primality 9001745604955853489 (3 : ZMod 9001745604955853489)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 2), (89, 1), (4049, 1), (1856406043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 2), (89, 1), (4049, 1), (1856406043, 1)] : List FactorBlock).map factorBlockValue).prod) = 9001745604955853489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_89
      · exact prime_sixtyOneBG_4049
      · exact prime_sixtyOneBG_1856406043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9001745604955853489) ^ 4500872802477926744 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9001745604955853489) ^ 310405020860546672 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9001745604955853489) ^ 101143209044447792 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9001745604955853489) ^ 2223202174600112 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9001745604955853489) ^ 4849017616 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_23299993986982396007 : Nat.Prime 23299993986982396007 := by
  apply lucas_primality 23299993986982396007 (5 : ZMod 23299993986982396007)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (389, 1), (1576240967865133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (389, 1), (1576240967865133, 1)] : List FactorBlock).map factorBlockValue).prod) = 23299993986982396007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_389
      · exact prime_sixtyOneBG_1576240967865133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 23299993986982396007) ^ 11649996993491198003 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 23299993986982396007) ^ 1226315472999073474 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 23299993986982396007) ^ 59897156778875054 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 23299993986982396007) ^ 14782 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_26673518767235154583 : Nat.Prime 26673518767235154583 := by
  apply lucas_primality 26673518767235154583 (3 : ZMod 26673518767235154583)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (9767, 1), (1013728210559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (9767, 1), (1013728210559, 1)] : List FactorBlock).map factorBlockValue).prod) = 26673518767235154583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_449
      · exact prime_sixtyOneBG_9767
      · exact prime_sixtyOneBG_1013728210559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26673518767235154583) ^ 13336759383617577291 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26673518767235154583) ^ 8891172922411718194 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26673518767235154583) ^ 59406500595178518 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26673518767235154583) ^ 2730983799245946 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26673518767235154583) ^ 26312298 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_44648321031145250173 : Nat.Prime 44648321031145250173 := by
  apply lucas_primality 44648321031145250173 (2 : ZMod 44648321031145250173)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (41, 1), (149, 1), (347, 1), (45004887373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (41, 1), (149, 1), (347, 1), (45004887373, 1)] : List FactorBlock).map factorBlockValue).prod) = 44648321031145250173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_149
      · exact prime_sixtyOneBG_347
      · exact prime_sixtyOneBG_45004887373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44648321031145250173) ^ 22324160515572625086 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44648321031145250173) ^ 14882773677048416724 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44648321031145250173) ^ 3434486233165019244 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44648321031145250173) ^ 1088983439784030492 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44648321031145250173) ^ 299653161282854028 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44648321031145250173) ^ 128669513058055476 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 44648321031145250173) ^ 992077164 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_46160591823594137353 : Nat.Prime 46160591823594137353 := by
  apply lucas_primality 46160591823594137353 (5 : ZMod 46160591823594137353)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1021, 1), (38543941, 1), (48874043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1021, 1), (38543941, 1), (48874043, 1)] : List FactorBlock).map factorBlockValue).prod) = 46160591823594137353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_1021
      · exact prime_sixtyOneBG_38543941
      · exact prime_sixtyOneBG_48874043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 46160591823594137353) ^ 23080295911797068676 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 46160591823594137353) ^ 15386863941198045784 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 46160591823594137353) ^ 45211157515763112 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 46160591823594137353) ^ 1197609549672 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 46160591823594137353) ^ 944480730264 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_52776224627660953403 : Nat.Prime 52776224627660953403 := by
  apply lucas_primality 52776224627660953403 (2 : ZMod 52776224627660953403)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (151, 1), (383, 1), (26840072291141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (151, 1), (383, 1), (26840072291141, 1)] : List FactorBlock).map factorBlockValue).prod) = 52776224627660953403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_151
      · exact prime_sixtyOneBG_383
      · exact prime_sixtyOneBG_26840072291141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52776224627660953403) ^ 26388112313830476701 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 52776224627660953403) ^ 3104483801627114906 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 52776224627660953403) ^ 349511421375238102 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 52776224627660953403) ^ 137796931142717894 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 52776224627660953403) ^ 1966322 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_58591194654460488721 : Nat.Prime 58591194654460488721 := by
  apply lucas_primality 58591194654460488721 (11 : ZMod 58591194654460488721)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (271, 1), (571, 1), (829, 1), (5281, 1), (51481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (271, 1), (571, 1), (829, 1), (5281, 1), (51481, 1)] : List FactorBlock).map factorBlockValue).prod) = 58591194654460488721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_271
      · exact prime_sixtyOneBG_571
      · exact prime_sixtyOneBG_829
      · exact prime_sixtyOneBG_5281
      · exact prime_sixtyOneBG_51481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 58591194654460488721) ^ 29295597327230244360 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 19530398218153496240 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 11718238930892097744 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 8370170664922926960 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 216203670311662320 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 102611549307286320 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 70676953744825680 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 11094715897455120 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (11 : ZMod 58591194654460488721) ^ 1138112986431120 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_73219421762010939661 : Nat.Prime 73219421762010939661 := by
  apply lucas_primality 73219421762010939661 (2 : ZMod 73219421762010939661)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (293, 1), (84998516126873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (293, 1), (84998516126873, 1)] : List FactorBlock).map factorBlockValue).prod) = 73219421762010939661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_293
      · exact prime_sixtyOneBG_84998516126873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73219421762010939661) ^ 36609710881005469830 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73219421762010939661) ^ 24406473920670313220 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73219421762010939661) ^ 14643884352402187932 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73219421762010939661) ^ 10459917394572991380 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73219421762010939661) ^ 249895637413006620 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73219421762010939661) ^ 861420 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_302314725176206943063 : Nat.Prime 302314725176206943063 := by
  apply lucas_primality 302314725176206943063 (5 : ZMod 302314725176206943063)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1815179, 1), (83274080731489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1815179, 1), (83274080731489, 1)] : List FactorBlock).map factorBlockValue).prod) = 302314725176206943063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_1815179
      · exact prime_sixtyOneBG_83274080731489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 302314725176206943063) ^ 151157362588103471531 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 302314725176206943063) ^ 166548161462978 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 302314725176206943063) ^ 3630358 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_610860935599645532273 : Nat.Prime 610860935599645532273 := by
  apply lucas_primality 610860935599645532273 (3 : ZMod 610860935599645532273)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (9006373, 1), (4239088085179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (9006373, 1), (4239088085179, 1)] : List FactorBlock).map factorBlockValue).prod) = 610860935599645532273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_9006373
      · exact prime_sixtyOneBG_4239088085179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 610860935599645532273) ^ 305430467799822766136 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 610860935599645532273) ^ 67825409362864 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 610860935599645532273) ^ 144101968 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_626883748714037608517 : Nat.Prime 626883748714037608517 := by
  apply lucas_primality 626883748714037608517 (2 : ZMod 626883748714037608517)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (88718293, 1), (56983897363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (88718293, 1), (56983897363, 1)] : List FactorBlock).map factorBlockValue).prod) = 626883748714037608517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_31
      · exact prime_sixtyOneBG_88718293
      · exact prime_sixtyOneBG_56983897363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 626883748714037608517) ^ 313441874357018804258 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 626883748714037608517) ^ 20222056410130245436 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 626883748714037608517) ^ 7066003273012 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 626883748714037608517) ^ 11001068332 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_640955997208203521627 : Nat.Prime 640955997208203521627 := by
  apply lucas_primality 640955997208203521627 (2 : ZMod 640955997208203521627)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (479, 1), (17209, 1), (3880847, 1), (10017989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (479, 1), (17209, 1), (3880847, 1), (10017989, 1)] : List FactorBlock).map factorBlockValue).prod) = 640955997208203521627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_479
      · exact prime_sixtyOneBG_17209
      · exact prime_sixtyOneBG_3880847
      · exact prime_sixtyOneBG_10017989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640955997208203521627) ^ 320477998604101760813 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640955997208203521627) ^ 1338112729035915494 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640955997208203521627) ^ 37245394689302314 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640955997208203521627) ^ 165158790647558 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640955997208203521627) ^ 63980505190034 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_653603285030023906103 : Nat.Prime 653603285030023906103 := by
  apply lucas_primality 653603285030023906103 (5 : ZMod 653603285030023906103)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (10425409, 1), (4478092795277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (10425409, 1), (4478092795277, 1)] : List FactorBlock).map factorBlockValue).prod) = 653603285030023906103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_10425409
      · exact prime_sixtyOneBG_4478092795277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 653603285030023906103) ^ 326801642515011953051 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 653603285030023906103) ^ 93371897861431986586 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 653603285030023906103) ^ 62693299133878 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 653603285030023906103) ^ 145955726 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1331628934377344461739 : Nat.Prime 1331628934377344461739 := by
  apply lucas_primality 1331628934377344461739 (2 : ZMod 1331628934377344461739)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (353, 1), (379, 1), (28057, 1), (46309, 1), (348209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (353, 1), (379, 1), (28057, 1), (46309, 1), (348209, 1)] : List FactorBlock).map factorBlockValue).prod) = 1331628934377344461739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_353
      · exact prime_sixtyOneBG_379
      · exact prime_sixtyOneBG_28057
      · exact prime_sixtyOneBG_46309
      · exact prime_sixtyOneBG_348209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1331628934377344461739) ^ 665814467188672230869 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331628934377344461739) ^ 121057175852485860158 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331628934377344461739) ^ 3772319927414573546 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331628934377344461739) ^ 3513532808383494622 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331628934377344461739) ^ 47461558056005434 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331628934377344461739) ^ 28755294529731682 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1331628934377344461739) ^ 3824223194625482 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2157504967593339705829 : Nat.Prime 2157504967593339705829 := by
  apply lucas_primality 2157504967593339705829 (2 : ZMod 2157504967593339705829)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (811, 1), (73897279339407443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (811, 1), (73897279339407443, 1)] : List FactorBlock).map factorBlockValue).prod) = 2157504967593339705829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_811
      · exact prime_sixtyOneBG_73897279339407443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2157504967593339705829) ^ 1078752483796669852914 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2157504967593339705829) ^ 719168322531113235276 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2157504967593339705829) ^ 2660302056218667948 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2157504967593339705829) ^ 29196 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2507634609252292199189 : Nat.Prime 2507634609252292199189 := by
  apply lucas_primality 2507634609252292199189 (2 : ZMod 2507634609252292199189)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10631, 1), (58969866645947987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10631, 1), (58969866645947987, 1)] : List FactorBlock).map factorBlockValue).prod) = 2507634609252292199189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_10631
      · exact prime_sixtyOneBG_58969866645947987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2507634609252292199189) ^ 1253817304626146099594 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2507634609252292199189) ^ 235879466583791948 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2507634609252292199189) ^ 42524 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3308602481257442008417 : Nat.Prime 3308602481257442008417 := by
  apply lucas_primality 3308602481257442008417 (5 : ZMod 3308602481257442008417)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (397, 1), (479267, 1), (25876604297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (397, 1), (479267, 1), (25876604297, 1)] : List FactorBlock).map factorBlockValue).prod) = 3308602481257442008417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_397
      · exact prime_sixtyOneBG_479267
      · exact prime_sixtyOneBG_25876604297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3308602481257442008417) ^ 1654301240628721004208 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3308602481257442008417) ^ 1102867493752480669472 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3308602481257442008417) ^ 472657497322491715488 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3308602481257442008417) ^ 8334011287802120928 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3308602481257442008417) ^ 6903464000770848 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3308602481257442008417) ^ 127860767328 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3665165613597873193639 : Nat.Prime 3665165613597873193639 := by
  apply lucas_primality 3665165613597873193639 (3 : ZMod 3665165613597873193639)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (610860935599645532273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (610860935599645532273, 1)] : List FactorBlock).map factorBlockValue).prod) = 3665165613597873193639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_610860935599645532273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3665165613597873193639) ^ 1832582806798936596819 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3665165613597873193639) ^ 1221721871199291064546 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3665165613597873193639) ^ 6 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3895810614266664695929 : Nat.Prime 3895810614266664695929 := by
  apply lucas_primality 3895810614266664695929 (7 : ZMod 3895810614266664695929)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (383, 1), (486041539, 1), (871995881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (383, 1), (486041539, 1), (871995881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3895810614266664695929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_383
      · exact prime_sixtyOneBG_486041539
      · exact prime_sixtyOneBG_871995881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3895810614266664695929) ^ 1947905307133332347964 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3895810614266664695929) ^ 1298603538088888231976 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3895810614266664695929) ^ 10171829280069620616 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3895810614266664695929) ^ 8015386138152 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3895810614266664695929) ^ 4467693826488 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_12659336866330777600267 : Nat.Prime 12659336866330777600267 := by
  apply lucas_primality 12659336866330777600267 (2 : ZMod 12659336866330777600267)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (431, 1), (6703, 1), (730320038062327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (431, 1), (6703, 1), (730320038062327, 1)] : List FactorBlock).map factorBlockValue).prod) = 12659336866330777600267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_431
      · exact prime_sixtyOneBG_6703
      · exact prime_sixtyOneBG_730320038062327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12659336866330777600267) ^ 6329668433165388800133 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659336866330777600267) ^ 4219778955443592533422 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659336866330777600267) ^ 29372011290790667286 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659336866330777600267) ^ 1888607618429177622 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659336866330777600267) ^ 17333958 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_15635287580657343528641 : Nat.Prime 15635287580657343528641 := by
  apply lucas_primality 15635287580657343528641 (3 : ZMod 15635287580657343528641)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (2143, 1), (8297, 1), (2747974094137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (2143, 1), (8297, 1), (2747974094137, 1)] : List FactorBlock).map factorBlockValue).prod) = 15635287580657343528641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_2143
      · exact prime_sixtyOneBG_8297
      · exact prime_sixtyOneBG_2747974094137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15635287580657343528641) ^ 7817643790328671764320 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15635287580657343528641) ^ 3127057516131468705728 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15635287580657343528641) ^ 7295981138897500480 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15635287580657343528641) ^ 1884450714795389120 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15635287580657343528641) ^ 5689750720 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_22479639397745797815007 : Nat.Prime 22479639397745797815007 := by
  apply lucas_primality 22479639397745797815007 (3 : ZMod 22479639397745797815007)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (502093, 1), (7461977295622457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (502093, 1), (7461977295622457, 1)] : List FactorBlock).map factorBlockValue).prod) = 22479639397745797815007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_502093
      · exact prime_sixtyOneBG_7461977295622457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22479639397745797815007) ^ 11239819698872898907503 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22479639397745797815007) ^ 7493213132581932605002 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22479639397745797815007) ^ 44771863773734742 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22479639397745797815007) ^ 3012558 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_34562166144023079718777 : Nat.Prime 34562166144023079718777 := by
  apply lucas_primality 34562166144023079718777 (7 : ZMod 34562166144023079718777)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (503, 1), (70241, 1), (129593, 1), (104840297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (503, 1), (70241, 1), (129593, 1), (104840297, 1)] : List FactorBlock).map factorBlockValue).prod) = 34562166144023079718777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_503
      · exact prime_sixtyOneBG_70241
      · exact prime_sixtyOneBG_129593
      · exact prime_sixtyOneBG_104840297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 34562166144023079718777) ^ 17281083072011539859388 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34562166144023079718777) ^ 11520722048007693239592 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34562166144023079718777) ^ 68712059928475307592 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34562166144023079718777) ^ 492051168747926136 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34562166144023079718777) ^ 266697785713912632 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34562166144023079718777) ^ 329664901121208 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_36667546225889144997467 : Nat.Prime 36667546225889144997467 := by
  apply lucas_primality 36667546225889144997467 (2 : ZMod 36667546225889144997467)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (127, 1), (197, 1), (301759, 1), (8461352279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (127, 1), (197, 1), (301759, 1), (8461352279, 1)] : List FactorBlock).map factorBlockValue).prod) = 36667546225889144997467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_41
      · exact prime_sixtyOneBG_127
      · exact prime_sixtyOneBG_197
      · exact prime_sixtyOneBG_301759
      · exact prime_sixtyOneBG_8461352279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36667546225889144997467) ^ 18333773112944572498733 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36667546225889144997467) ^ 5238220889412734999638 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36667546225889144997467) ^ 894330395753393780426 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36667546225889144997467) ^ 288720836424323976358 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36667546225889144997467) ^ 186129676273548959378 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36667546225889144997467) ^ 121512684711604774 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36667546225889144997467) ^ 4333532633654 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_38447826531910622514689 : Nat.Prime 38447826531910622514689 := by
  apply lucas_primality 38447826531910622514689 (3 : ZMod 38447826531910622514689)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (7, 1), (11, 1), (13, 1), (19, 1), (62761, 1), (62910668461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (7, 1), (11, 1), (13, 1), (19, 1), (62761, 1), (62910668461, 1)] : List FactorBlock).map factorBlockValue).prod) = 38447826531910622514689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_11
      · exact prime_sixtyOneBG_13
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_62761
      · exact prime_sixtyOneBG_62910668461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38447826531910622514689) ^ 19223913265955311257344 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 38447826531910622514689) ^ 5492546647415803216384 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 38447826531910622514689) ^ 3495256957446420228608 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 38447826531910622514689) ^ 2957525117839278654976 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 38447826531910622514689) ^ 2023569817468980132352 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 38447826531910622514689) ^ 612606977771396608 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 38447826531910622514689) ^ 611149547008 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_47277406688661909128581 : Nat.Prime 47277406688661909128581 := by
  apply lucas_primality 47277406688661909128581 (2 : ZMod 47277406688661909128581)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (601, 1), (24423701, 1), (53680487243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (601, 1), (24423701, 1), (53680487243, 1)] : List FactorBlock).map factorBlockValue).prod) = 47277406688661909128581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_601
      · exact prime_sixtyOneBG_24423701
      · exact prime_sixtyOneBG_53680487243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47277406688661909128581) ^ 23638703344330954564290 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47277406688661909128581) ^ 15759135562887303042860 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47277406688661909128581) ^ 9455481337732381825716 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47277406688661909128581) ^ 78664570197440780580 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47277406688661909128581) ^ 1935718369982580 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 47277406688661909128581) ^ 880718658060 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_64614529952373116344043 : Nat.Prime 64614529952373116344043 := by
  apply lucas_primality 64614529952373116344043 (2 : ZMod 64614529952373116344043)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (97, 1), (9001745604955853489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (97, 1), (9001745604955853489, 1)] : List FactorBlock).map factorBlockValue).prod) = 64614529952373116344043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_37
      · exact prime_sixtyOneBG_97
      · exact prime_sixtyOneBG_9001745604955853489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64614529952373116344043) ^ 32307264976186558172021 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64614529952373116344043) ^ 1746338647361435576866 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64614529952373116344043) ^ 666129174766733158186 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 64614529952373116344043) ^ 7178 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_307582612255284980117513 : Nat.Prime 307582612255284980117513 := by
  apply lucas_primality 307582612255284980117513 (3 : ZMod 307582612255284980117513)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (38447826531910622514689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (38447826531910622514689, 1)] : List FactorBlock).map factorBlockValue).prod) = 307582612255284980117513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_38447826531910622514689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 307582612255284980117513) ^ 153791306127642490058756 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 307582612255284980117513) ^ 8 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_359674230363932765040113 : Nat.Prime 359674230363932765040113 := by
  apply lucas_primality 359674230363932765040113 (3 : ZMod 359674230363932765040113)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (22479639397745797815007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (22479639397745797815007, 1)] : List FactorBlock).map factorBlockValue).prod) = 359674230363932765040113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_22479639397745797815007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 359674230363932765040113) ^ 179837115181966382520056 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 359674230363932765040113) ^ 16 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2279338809427059377945419 : Nat.Prime 2279338809427059377945419 := by
  apply lucas_primality 2279338809427059377945419 (2 : ZMod 2279338809427059377945419)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (239, 1), (99767, 1), (5310697517561477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (239, 1), (99767, 1), (5310697517561477, 1)] : List FactorBlock).map factorBlockValue).prod) = 2279338809427059377945419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_239
      · exact prime_sixtyOneBG_99767
      · exact prime_sixtyOneBG_5310697517561477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2279338809427059377945419) ^ 1139669404713529688972709 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2279338809427059377945419) ^ 759779603142353125981806 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2279338809427059377945419) ^ 9536982466222005765462 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2279338809427059377945419) ^ 22846620720549474054 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2279338809427059377945419) ^ 429197634 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3119302765150179875354371 : Nat.Prime 3119302765150179875354371 := by
  apply lucas_primality 3119302765150179875354371 (3 : ZMod 3119302765150179875354371)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (283, 1), (17383, 1), (21136112398986811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (283, 1), (17383, 1), (21136112398986811, 1)] : List FactorBlock).map factorBlockValue).prod) = 3119302765150179875354371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_283
      · exact prime_sixtyOneBG_17383
      · exact prime_sixtyOneBG_21136112398986811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3119302765150179875354371) ^ 1559651382575089937677185 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119302765150179875354371) ^ 1039767588383393291784790 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119302765150179875354371) ^ 623860553030035975070874 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119302765150179875354371) ^ 11022271254947632068390 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119302765150179875354371) ^ 179445594267398025390 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119302765150179875354371) ^ 147581670 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_3690991347063419761410157 : Nat.Prime 3690991347063419761410157 := by
  apply lucas_primality 3690991347063419761410157 (2 : ZMod 3690991347063419761410157)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (307582612255284980117513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (307582612255284980117513, 1)] : List FactorBlock).map factorBlockValue).prod) = 3690991347063419761410157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_307582612255284980117513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3690991347063419761410157) ^ 1845495673531709880705078 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3690991347063419761410157) ^ 1230330449021139920470052 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3690991347063419761410157) ^ 12 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_6537782606316032881714537 : Nat.Prime 6537782606316032881714537 := by
  apply lucas_primality 6537782606316032881714537 (7 : ZMod 6537782606316032881714537)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (6230450183, 1), (14573992814611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (6230450183, 1), (14573992814611, 1)] : List FactorBlock).map factorBlockValue).prod) = 6537782606316032881714537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_6230450183
      · exact prime_sixtyOneBG_14573992814611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6537782606316032881714537) ^ 3268891303158016440857268 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6537782606316032881714537) ^ 2179260868772010960571512 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6537782606316032881714537) ^ 1049327482651992 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 6537782606316032881714537) ^ 448592413176 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_8993425605471026152661561 : Nat.Prime 8993425605471026152661561 := by
  apply lucas_primality 8993425605471026152661561 (3 : ZMod 8993425605471026152661561)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (198221, 1), (59698290009841661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (198221, 1), (59698290009841661, 1)] : List FactorBlock).map factorBlockValue).prod) = 8993425605471026152661561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_198221
      · exact prime_sixtyOneBG_59698290009841661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8993425605471026152661561) ^ 4496712802735513076330780 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993425605471026152661561) ^ 1798685121094205230532312 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993425605471026152661561) ^ 473338189761632955403240 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993425605471026152661561) ^ 45370700407479662360 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993425605471026152661561) ^ 150647960 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_9562222212976950241075717 : Nat.Prime 9562222212976950241075717 := by
  apply lucas_primality 9562222212976950241075717 (5 : ZMod 9562222212976950241075717)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5788423, 1), (137663030342014141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5788423, 1), (137663030342014141, 1)] : List FactorBlock).map factorBlockValue).prod) = 9562222212976950241075717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5788423
      · exact prime_sixtyOneBG_137663030342014141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9562222212976950241075717) ^ 4781111106488475120537858 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9562222212976950241075717) ^ 3187407404325650080358572 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9562222212976950241075717) ^ 1651956364104169692 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 9562222212976950241075717) ^ 69461076 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_59405502413733244413668087 : Nat.Prime 59405502413733244413668087 := by
  apply lucas_primality 59405502413733244413668087 (7 : ZMod 59405502413733244413668087)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 2), (12157, 1), (52177, 1), (156677, 1), (118271653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 2), (12157, 1), (52177, 1), (156677, 1), (118271653, 1)] : List FactorBlock).map factorBlockValue).prod) = 59405502413733244413668087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_19
      · exact prime_sixtyOneBG_12157
      · exact prime_sixtyOneBG_52177
      · exact prime_sixtyOneBG_156677
      · exact prime_sixtyOneBG_118271653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 59405502413733244413668087) ^ 29702751206866622206834043 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 59405502413733244413668087) ^ 8486500344819034916238298 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 59405502413733244413668087) ^ 3126605390196486548087794 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 59405502413733244413668087) ^ 4886526479701673473198 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 59405502413733244413668087) ^ 1138538099425671165718 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 59405502413733244413668087) ^ 379159049597153662718 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (7 : ZMod 59405502413733244413668087) ^ 502280139888915262 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_159553716659894156456179331 : Nat.Prime 159553716659894156456179331 := by
  apply lucas_primality 159553716659894156456179331 (2 : ZMod 159553716659894156456179331)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2279338809427059377945419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2279338809427059377945419, 1)] : List FactorBlock).map factorBlockValue).prod) = 159553716659894156456179331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_2279338809427059377945419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 159553716659894156456179331) ^ 79776858329947078228089665 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 159553716659894156456179331) ^ 31910743331978831291235866 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 159553716659894156456179331) ^ 22793388094270593779454190 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 159553716659894156456179331) ^ 70 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_221902399785452796055978639 : Nat.Prime 221902399785452796055978639 := by
  apply lucas_primality 221902399785452796055978639 (3 : ZMod 221902399785452796055978639)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (2125841, 1), (1023366151742671309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (2125841, 1), (1023366151742671309, 1)] : List FactorBlock).map factorBlockValue).prod) = 221902399785452796055978639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_2125841
      · exact prime_sixtyOneBG_1023366151742671309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 221902399785452796055978639) ^ 110951199892726398027989319 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 221902399785452796055978639) ^ 73967466595150932018659546 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 221902399785452796055978639) ^ 13053082340320752709175214 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 221902399785452796055978639) ^ 104383347477752473518 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 221902399785452796055978639) ^ 216835782 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_424225176060424463048194457 : Nat.Prime 424225176060424463048194457 := by
  apply lucas_primality 424225176060424463048194457 (3 : ZMod 424225176060424463048194457)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (3119302765150179875354371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (3119302765150179875354371, 1)] : List FactorBlock).map factorBlockValue).prod) = 424225176060424463048194457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_17
      · exact prime_sixtyOneBG_3119302765150179875354371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 424225176060424463048194457) ^ 212112588030212231524097228 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 424225176060424463048194457) ^ 24954422121201439002834968 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 424225176060424463048194457) ^ 136 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_693444999329539987674933247 : Nat.Prime 693444999329539987674933247 := by
  apply lucas_primality 693444999329539987674933247 (5 : ZMod 693444999329539987674933247)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (8273, 1), (930301, 1), (154811252349961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (8273, 1), (930301, 1), (154811252349961, 1)] : List FactorBlock).map factorBlockValue).prod) = 693444999329539987674933247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_97
      · exact prime_sixtyOneBG_8273
      · exact prime_sixtyOneBG_930301
      · exact prime_sixtyOneBG_154811252349961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 693444999329539987674933247) ^ 346722499664769993837466623 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 693444999329539987674933247) ^ 231148333109846662558311082 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 693444999329539987674933247) ^ 7148917518861236986339518 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 693444999329539987674933247) ^ 83820258591749061727902 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 693444999329539987674933247) ^ 745398531582294319446 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 693444999329539987674933247) ^ 4479293260686 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1471801631230044055473327707 : Nat.Prime 1471801631230044055473327707 := by
  apply lucas_primality 1471801631230044055473327707 (2 : ZMod 1471801631230044055473327707)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (757, 1), (21773, 1), (44648321031145250173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (757, 1), (21773, 1), (44648321031145250173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1471801631230044055473327707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_757
      · exact prime_sixtyOneBG_21773
      · exact prime_sixtyOneBG_44648321031145250173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1471801631230044055473327707) ^ 735900815615022027736663853 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1471801631230044055473327707) ^ 1944255787622251064033458 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1471801631230044055473327707) ^ 67597558041153908761922 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1471801631230044055473327707) ^ 32964322 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1602628442894936860404290171 : Nat.Prime 1602628442894936860404290171 := by
  apply lucas_primality 1602628442894936860404290171 (2 : ZMod 1602628442894936860404290171)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (29, 1), (61, 1), (853, 1), (659675122022990221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (29, 1), (61, 1), (853, 1), (659675122022990221, 1)] : List FactorBlock).map factorBlockValue).prod) = 1602628442894936860404290171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_61
      · exact prime_sixtyOneBG_853
      · exact prime_sixtyOneBG_659675122022990221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1602628442894936860404290171) ^ 801314221447468430202145085 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1602628442894936860404290171) ^ 320525688578987372080858034 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1602628442894936860404290171) ^ 228946920413562408629184310 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1602628442894936860404290171) ^ 69679497517171167843664790 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1602628442894936860404290171) ^ 55263049754997822772561730 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1602628442894936860404290171) ^ 26272597424507161645971970 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1602628442894936860404290171) ^ 1878814118282458218527890 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1602628442894936860404290171) ^ 2429420770 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_1802956998256803967954826441 : Nat.Prime 1802956998256803967954826441 := by
  apply lucas_primality 1802956998256803967954826441 (6 : ZMod 1802956998256803967954826441)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (149, 1), (26083, 1), (28927, 1), (5311499, 1), (75485071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (149, 1), (26083, 1), (28927, 1), (5311499, 1), (75485071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1802956998256803967954826441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_149
      · exact prime_sixtyOneBG_26083
      · exact prime_sixtyOneBG_28927
      · exact prime_sixtyOneBG_5311499
      · exact prime_sixtyOneBG_75485071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1802956998256803967954826441) ^ 901478499128401983977413220 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1802956998256803967954826441) ^ 360591399651360793590965288 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1802956998256803967954826441) ^ 12100382538636268241307560 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1802956998256803967954826441) ^ 69123835381543686230680 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1802956998256803967954826441) ^ 62327825154934973137720 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1802956998256803967954826441) ^ 339444100103719113560 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1802956998256803967954826441) ^ 23884948035046611640 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_2060522283722061677662658791 : Nat.Prime 2060522283722061677662658791 := by
  apply lucas_primality 2060522283722061677662658791 (3 : ZMod 2060522283722061677662658791)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (29, 1), (61, 1), (853, 1), (659675122022990221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (29, 1), (61, 1), (853, 1), (659675122022990221, 1)] : List FactorBlock).map factorBlockValue).prod) = 2060522283722061677662658791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_61
      · exact prime_sixtyOneBG_853
      · exact prime_sixtyOneBG_659675122022990221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2060522283722061677662658791) ^ 1030261141861030838831329395 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2060522283722061677662658791) ^ 686840761240687225887552930 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2060522283722061677662658791) ^ 412104456744412335532531758 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2060522283722061677662658791) ^ 89587925379220072941854730 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2060522283722061677662658791) ^ 71052492542140057850436510 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2060522283722061677662658791) ^ 33779053831509207830535390 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2060522283722061677662658791) ^ 2415618152077446280964430 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2060522283722061677662658791) ^ 3123540990 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_5547559994636319901399465973 : Nat.Prime 5547559994636319901399465973 := by
  apply lucas_primality 5547559994636319901399465973 (2 : ZMod 5547559994636319901399465973)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (53, 1), (173, 2), (351653, 1), (355190689847659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (53, 1), (173, 2), (351653, 1), (355190689847659, 1)] : List FactorBlock).map factorBlockValue).prod) = 5547559994636319901399465973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_53
      · exact prime_sixtyOneBG_173
      · exact prime_sixtyOneBG_351653
      · exact prime_sixtyOneBG_355190689847659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5547559994636319901399465973) ^ 2773779997318159950699732986 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547559994636319901399465973) ^ 792508570662331414485637996 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547559994636319901399465973) ^ 104670943295024903799989924 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547559994636319901399465973) ^ 32066820778244623707511364 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547559994636319901399465973) ^ 15775665200172669937124 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547559994636319901399465973) ^ 15618539993308 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_9014784991284019839774132203 : Nat.Prime 9014784991284019839774132203 := by
  apply lucas_primality 9014784991284019839774132203 (2 : ZMod 9014784991284019839774132203)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2089169, 1), (2157504967593339705829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2089169, 1), (2157504967593339705829, 1)] : List FactorBlock).map factorBlockValue).prod) = 9014784991284019839774132203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_2089169
      · exact prime_sixtyOneBG_2157504967593339705829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9014784991284019839774132203) ^ 4507392495642009919887066101 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9014784991284019839774132203) ^ 4315009935186679411658 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9014784991284019839774132203) ^ 4178338 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_9014784991284019839774132209 : Nat.Prime 9014784991284019839774132209 := by
  apply lucas_primality 9014784991284019839774132209 (3 : ZMod 9014784991284019839774132209)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (79, 1), (3229, 1), (1902779, 1), (165826473217481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (79, 1), (3229, 1), (1902779, 1), (165826473217481, 1)] : List FactorBlock).map factorBlockValue).prod) = 9014784991284019839774132209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_79
      · exact prime_sixtyOneBG_3229
      · exact prime_sixtyOneBG_1902779
      · exact prime_sixtyOneBG_165826473217481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9014784991284019839774132209) ^ 4507392495642009919887066104 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9014784991284019839774132209) ^ 1287826427326288548539161744 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9014784991284019839774132209) ^ 114111202421316706832583952 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9014784991284019839774132209) ^ 2791819446046460154776752 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9014784991284019839774132209) ^ 4737694178506289926352 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9014784991284019839774132209) ^ 54362761363568 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_14423655986054431743638611531 : Nat.Prime 14423655986054431743638611531 := by
  apply lucas_primality 14423655986054431743638611531 (2 : ZMod 14423655986054431743638611531)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (23, 1), (29, 1), (61, 1), (853, 1), (659675122022990221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (23, 1), (29, 1), (61, 1), (853, 1), (659675122022990221, 1)] : List FactorBlock).map factorBlockValue).prod) = 14423655986054431743638611531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_5
      · exact prime_sixtyOneBG_7
      · exact prime_sixtyOneBG_23
      · exact prime_sixtyOneBG_29
      · exact prime_sixtyOneBG_61
      · exact prime_sixtyOneBG_853
      · exact prime_sixtyOneBG_659675122022990221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14423655986054431743638611531) ^ 7211827993027215871819305765 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 4807885328684810581212870510 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 2884731197210886348727722306 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 2060522283722061677662658790 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 627115477654540510592983110 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 497367447794980404953055570 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 236453376820564454813747730 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 16909327064542123966751010 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14423655986054431743638611531) ^ 21864786930 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_36059139965136079359096528817 : Nat.Prime 36059139965136079359096528817 := by
  apply lucas_primality 36059139965136079359096528817 (5 : ZMod 36059139965136079359096528817)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (52185857, 1), (1599479939570178209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (52185857, 1), (1599479939570178209, 1)] : List FactorBlock).map factorBlockValue).prod) = 36059139965136079359096528817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_52185857
      · exact prime_sixtyOneBG_1599479939570178209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 36059139965136079359096528817) ^ 18029569982568039679548264408 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36059139965136079359096528817) ^ 12019713321712026453032176272 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36059139965136079359096528817) ^ 690975333894316986288 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36059139965136079359096528817) ^ 22544290224 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem prime_sixtyOneBG_72118279930272158718193057687 : Nat.Prime 72118279930272158718193057687 := by
  apply lucas_primality 72118279930272158718193057687 (3 : ZMod 72118279930272158718193057687)
  · rw [← sixtyOneBGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (353, 1), (599, 1), (6133, 1), (50891, 1), (20236533621649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (353, 1), (599, 1), (6133, 1), (50891, 1), (20236533621649, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyOneBG_2
      · exact prime_sixtyOneBG_3
      · exact prime_sixtyOneBG_353
      · exact prime_sixtyOneBG_599
      · exact prime_sixtyOneBG_6133
      · exact prime_sixtyOneBG_50891
      · exact prime_sixtyOneBG_20236533621649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72118279930272158718193057687) ^ 36059139965136079359096528843 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272158718193057687) ^ 24039426643424052906064352562 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272158718193057687) ^ 204301076289722829230008662 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272158718193057687) ^ 120397796210804939429370714 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272158718193057687) ^ 11759054285059866088079742 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272158718193057687) ^ 1417112651161740950623746 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272158718193057687) ^ 3563766467055414 ≠ 1
      rw [← sixtyOneBGFastPow_eq_pow]
      decide

private theorem phi_sixtyOneBG_72118279930272158718193057600 : Nat.totient 72118279930272158718193057600 = 28651611004685072150661734400 := by
  rw [← show ((([(2, 6), (5, 2), (149, 1), (26083, 1), (28927, 1), (5311499, 1), (75485071, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_149, prime_sixtyOneBG_26083, prime_sixtyOneBG_28927, prime_sixtyOneBG_5311499, prime_sixtyOneBG_75485071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057601 : Nat.totient 72118279930272158718193057601 = 56934606000742053469552558080 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (349, 1), (1609, 1), (392389, 1), (60022152659533, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_7, prime_sixtyOneBG_19, prime_sixtyOneBG_41, prime_sixtyOneBG_349, prime_sixtyOneBG_1609, prime_sixtyOneBG_392389, prime_sixtyOneBG_60022152659533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057602 : Nat.totient 72118279930272158718193057602 = 24028914801191867080027565184 := by
  rw [← show ((([(2, 1), (3, 1), (2287, 1), (47515913, 1), (110608592638218557, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_2287, prime_sixtyOneBG_47515913, prime_sixtyOneBG_110608592638218557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057603 : Nat.totient 72118279930272158718193057603 = 70895723623034838537830296008 := by
  rw [← show ((([(59, 1), (333503, 1), (3665165613597873193639, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_59, prime_sixtyOneBG_333503, prime_sixtyOneBG_3665165613597873193639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057604 : Nat.totient 72118279930272158718193057604 = 31355748102601377566498956800 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (1216277, 1), (58591194654460488721, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_11, prime_sixtyOneBG_23, prime_sixtyOneBG_1216277, prime_sixtyOneBG_58591194654460488721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057605 : Nat.totient 72118279930272158718193057605 = 36158307343903996551741192192 := by
  rw [← show ((([(3, 3), (5, 1), (17, 1), (857, 1), (36667546225889144997467, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_5, prime_sixtyOneBG_17, prime_sixtyOneBG_857, prime_sixtyOneBG_36667546225889144997467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057606 : Nat.totient 72118279930272158718193057606 = 35164800612977558812365905280 := by
  rw [← show ((([(2, 1), (47, 1), (283, 1), (14549, 1), (12616758487, 1), (14768967581, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_47, prime_sixtyOneBG_283, prime_sixtyOneBG_14549, prime_sixtyOneBG_12616758487, prime_sixtyOneBG_14768967581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057607 : Nat.totient 72118279930272158718193057607 = 70168283476065710939149720416 := by
  rw [← show ((([(37, 2), (82189, 1), (640955997208203521627, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_37, prime_sixtyOneBG_82189, prime_sixtyOneBG_640955997208203521627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057608 : Nat.totient 72118279930272158718193057608 = 20476380588585589641797568000 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (251, 1), (439, 1), (3895810614266664695929, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_7, prime_sixtyOneBG_251, prime_sixtyOneBG_439, prime_sixtyOneBG_3895810614266664695929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057609 : Nat.totient 72118279930272158718193057609 = 72118279857052736955197156880 := by
  rw [← show ((([(984961069, 1), (73219421762010939661, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_984961069, prime_sixtyOneBG_73219421762010939661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057610 : Nat.totient 72118279930272158718193057610 = 26599958733529713093234666240 := by
  rw [← show ((([(2, 1), (5, 1), (13, 2), (941, 1), (847703, 1), (53496492916545803, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_13, prime_sixtyOneBG_941, prime_sixtyOneBG_847703, prime_sixtyOneBG_53496492916545803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057611 : Nat.totient 72118279930272158718193057611 = 47637752919033225072449928960 := by
  rw [← show ((([(3, 1), (109, 1), (4777781, 1), (46160591823594137353, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_109, prime_sixtyOneBG_4777781, prime_sixtyOneBG_46160591823594137353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057612 : Nat.totient 72118279930272158718193057612 = 35740032531816291046184169920 := by
  rw [← show ((([(2, 2), (113, 1), (159553716659894156456179331, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_113, prime_sixtyOneBG_159553716659894156456179331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057613 : Nat.totient 72118279930272158718193057613 = 72072244355342577500834250480 := by
  rw [← show ((([(1567, 1), (5830007, 1), (1573976431, 1), (5015440267, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_1567, prime_sixtyOneBG_5830007, prime_sixtyOneBG_1573976431, prime_sixtyOneBG_5015440267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057614 : Nat.totient 72118279930272158718193057614 = 23982053310146191204617895728 := by
  rw [← show ((([(2, 1), (3, 2), (419, 1), (9562222212976950241075717, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_419, prime_sixtyOneBG_9562222212976950241075717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057615 : Nat.totient 72118279930272158718193057615 = 44953811585815244489648576640 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (14797, 1), (12659336866330777600267, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_5, prime_sixtyOneBG_7, prime_sixtyOneBG_11, prime_sixtyOneBG_14797, prime_sixtyOneBG_12659336866330777600267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057616 : Nat.totient 72118279930272158718193057616 = 36059122705096338612362168832 := by
  rw [← show ((([(2, 4), (2089169, 1), (2157504967593339705829, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_2089169, prime_sixtyOneBG_2157504967593339705829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057617 : Nat.totient 72118279930272158718193057617 = 46396390297446987490863846720 := by
  rw [← show ((([(3, 1), (31, 1), (367, 1), (9967, 1), (474983, 1), (446327681339987, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_31, prime_sixtyOneBG_367, prime_sixtyOneBG_9967, prime_sixtyOneBG_474983, prime_sixtyOneBG_446327681339987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057618 : Nat.totient 72118279930272158718193057618 = 35999734462722346114682860116 := by
  rw [← show ((([(2, 1), (607, 1), (59405502413733244413668087, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_607, prime_sixtyOneBG_59405502413733244413668087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057619 : Nat.totient 72118279930272158718193057619 = 72118279929474831176871938640 := by
  rw [← show ((([(90450015049, 1), (797327450871103931, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_90450015049, prime_sixtyOneBG_797327450871103931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057620 : Nat.totient 72118279930272158718193057620 = 18219354921001416194652000384 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (19, 1), (2081843299, 1), (30387325065258067, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_5, prime_sixtyOneBG_19, prime_sixtyOneBG_2081843299, prime_sixtyOneBG_30387325065258067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057621 : Nat.totient 72118279930272158718193057621 = 69538391592772902514077021120 := by
  rw [← show ((([(29, 1), (991, 1), (6067, 1), (6143, 1), (67331640710173219, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_29, prime_sixtyOneBG_991, prime_sixtyOneBG_6067, prime_sixtyOneBG_6143, prime_sixtyOneBG_67331640710173219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057622 : Nat.totient 72118279930272158718193057622 = 29049314103258276185272512000 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (751, 1), (17317, 1), (23299993986982396007, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_7, prime_sixtyOneBG_17, prime_sixtyOneBG_751, prime_sixtyOneBG_17317, prime_sixtyOneBG_23299993986982396007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057623 : Nat.totient 72118279930272158718193057623 = 44114728580101992988374184512 := by
  rw [← show ((([(3, 2), (13, 1), (167, 1), (3690991347063419761410157, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_13, prime_sixtyOneBG_167, prime_sixtyOneBG_3690991347063419761410157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057624 : Nat.totient 72118279930272158718193057624 = 36059139965136079359096528808 := by
  rw [← show ((([(2, 3), (9014784991284019839774132203, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_9014784991284019839774132203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057625 : Nat.totient 72118279930272158718193057625 = 57691167727603324666580899200 := by
  rw [← show ((([(5, 3), (16693, 1), (34562166144023079718777, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_5, prime_sixtyOneBG_16693, prime_sixtyOneBG_34562166144023079718777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057626 : Nat.totient 72118279930272158718193057626 = 21264628160409660508255462080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (43, 1), (263, 1), (90235247, 1), (1070781868981807, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_11, prime_sixtyOneBG_43, prime_sixtyOneBG_263, prime_sixtyOneBG_90235247, prime_sixtyOneBG_1070781868981807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057627 : Nat.totient 72118279930272158718193057627 = 68083900815015023796072990720 := by
  rw [← show ((([(23, 1), (89, 1), (557, 1), (54091, 1), (59827907, 1), (19545352249, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_23, prime_sixtyOneBG_89, prime_sixtyOneBG_557, prime_sixtyOneBG_54091, prime_sixtyOneBG_59827907, prime_sixtyOneBG_19545352249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057628 : Nat.totient 72118279930272158718193057628 = 36059139965058826702666259232 := by
  rw [← show ((([(2, 2), (466774573049, 1), (38625861440561743, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_466774573049, prime_sixtyOneBG_38625861440561743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057629 : Nat.totient 72118279930272158718193057629 = 41003357998261900322065406400 := by
  rw [← show ((([(3, 1), (7, 1), (199, 1), (4328176141, 1), (3987200381088011, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_7, prime_sixtyOneBG_199, prime_sixtyOneBG_4328176141, prime_sixtyOneBG_3987200381088011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057630 : Nat.totient 72118279930272158718193057630 = 28845873275187407756216982400 := by
  rw [← show ((([(2, 1), (5, 1), (20051, 1), (359674230363932765040113, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_20051, prime_sixtyOneBG_359674230363932765040113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057631 : Nat.totient 72118279930272158718193057631 = 72036605773834400643318507672 := by
  rw [← show ((([(883, 1), (311766662483, 1), (261972064479079, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_883, prime_sixtyOneBG_311766662483, prime_sixtyOneBG_261972064479079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057632 : Nat.totient 72118279930272158718193057632 = 24039426182773830294823501824 := by
  rw [← show ((([(2, 5), (3, 3), (52185857, 1), (1599479939570178209, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_52185857, prime_sixtyOneBG_1599479939570178209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057633 : Nat.totient 72118279930272158718193057633 = 71894261354927281123827147888 := by
  rw [← show ((([(359, 1), (3109, 1), (64614529952373116344043, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_359, prime_sixtyOneBG_3109, prime_sixtyOneBG_64614529952373116344043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057634 : Nat.totient 72118279930272158718193057634 = 36059139965136079359096528816 := by
  rw [← show ((([(2, 1), (36059139965136079359096528817, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_36059139965136079359096528817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057635 : Nat.totient 72118279930272158718193057635 = 38463082628654241242773026528 := by
  rw [← show ((([(3, 1), (5, 1), (46664734867, 1), (103030379201507327, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_5, prime_sixtyOneBG_46664734867, prime_sixtyOneBG_103030379201507327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057636 : Nat.totient 72118279930272158718193057636 = 27830118221354439428346574848 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (53, 1), (173, 2), (351653, 1), (355190689847659, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_7, prime_sixtyOneBG_13, prime_sixtyOneBG_53, prime_sixtyOneBG_173, prime_sixtyOneBG_351653, prime_sixtyOneBG_355190689847659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057637 : Nat.totient 72118279930272158718193057637 = 64663030509107200648746019200 := by
  rw [← show ((([(11, 1), (73, 1), (70067, 1), (7447267, 1), (172115255991311, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_11, prime_sixtyOneBG_73, prime_sixtyOneBG_70067, prime_sixtyOneBG_7447267, prime_sixtyOneBG_172115255991311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057638 : Nat.totient 72118279930272158718193057638 = 23770666574457122707929521280 := by
  rw [← show ((([(2, 1), (3, 1), (163, 1), (197, 1), (1863506611, 1), (200867345908613, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_163, prime_sixtyOneBG_197, prime_sixtyOneBG_1863506611, prime_sixtyOneBG_200867345908613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057639 : Nat.totient 72118279930272158718193057639 = 63797274956408928918400811520 := by
  rw [← show ((([(17, 1), (19, 1), (127, 1), (20749831, 1), (84727531338529589, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_17, prime_sixtyOneBG_19, prime_sixtyOneBG_127, prime_sixtyOneBG_20749831, prime_sixtyOneBG_84727531338529589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057640 : Nat.totient 72118279930272158718193057640 = 28847311972108863487277223040 := by
  rw [← show ((([(2, 3), (5, 1), (1802956998256803967954826441, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_1802956998256803967954826441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057641 : Nat.totient 72118279930272158718193057641 = 47879865616731771632912179200 := by
  rw [← show ((([(3, 2), (257, 1), (4021, 1), (8571238411, 1), (904673937047, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_257, prime_sixtyOneBG_4021, prime_sixtyOneBG_8571238411, prime_sixtyOneBG_904673937047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057642 : Nat.totient 72118279930272158718193057642 = 35177707206815521467018240000 := by
  rw [← show ((([(2, 1), (41, 1), (18121, 1), (213095521, 1), (227758726451941, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_41, prime_sixtyOneBG_18121, prime_sixtyOneBG_213095521, prime_sixtyOneBG_227758726451941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057643 : Nat.totient 72118279930272158718193057643 = 61815668511661850329879763652 := by
  rw [← show ((([(7, 2), (1471801631230044055473327707, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_7, prime_sixtyOneBG_1471801631230044055473327707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057644 : Nat.totient 72118279930272158718193057644 = 22936331909365884788038041600 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (101, 2), (139, 1), (443, 1), (7867, 1), (60623, 1), (542193793, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_37, prime_sixtyOneBG_101, prime_sixtyOneBG_139, prime_sixtyOneBG_443, prime_sixtyOneBG_7867, prime_sixtyOneBG_60623, prime_sixtyOneBG_542193793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057645 : Nat.totient 72118279930272158718193057645 = 56505653647312616240034078720 := by
  rw [← show ((([(5, 1), (83, 1), (157, 1), (433, 1), (1856537993, 1), (1376911011911, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_5, prime_sixtyOneBG_83, prime_sixtyOneBG_157, prime_sixtyOneBG_433, prime_sixtyOneBG_1856537993, prime_sixtyOneBG_1376911011911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057646 : Nat.totient 72118279930272158718193057646 = 35925766458219793868489349760 := by
  rw [← show ((([(2, 1), (293, 1), (3491, 1), (3310877, 1), (10647676509681773, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_293, prime_sixtyOneBG_3491, prime_sixtyOneBG_3310877, prime_sixtyOneBG_10647676509681773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057647 : Nat.totient 72118279930272158718193057647 = 48065777721635473746365268672 := by
  rw [← show ((([(3, 1), (3677, 1), (6537782606316032881714537, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_3677, prime_sixtyOneBG_6537782606316032881714537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057648 : Nat.totient 72118279930272158718193057648 = 31559390823224655642032640000 := by
  rw [← show ((([(2, 4), (11, 1), (31, 1), (223, 1), (2141, 1), (4547, 1), (130693, 1), (46587798311, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_11, prime_sixtyOneBG_31, prime_sixtyOneBG_223, prime_sixtyOneBG_2141, prime_sixtyOneBG_4547, prime_sixtyOneBG_130693, prime_sixtyOneBG_46587798311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057649 : Nat.totient 72118279930272158718193057649 = 66570719935635838816793591664 := by
  rw [← show ((([(13, 1), (5547559994636319901399465973, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_13, prime_sixtyOneBG_5547559994636319901399465973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057650 : Nat.totient 72118279930272158718193057650 = 14956644109315824135779328000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (7, 1), (23, 1), (29, 1), (61, 1), (853, 1), (659675122022990221, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_5, prime_sixtyOneBG_7, prime_sixtyOneBG_23, prime_sixtyOneBG_29, prime_sixtyOneBG_61, prime_sixtyOneBG_853, prime_sixtyOneBG_659675122022990221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057651 : Nat.totient 72118279930272158718193057651 = 72118276621669677460729252032 := by
  rw [← show ((([(21797203, 1), (3308602481257442008417, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_21797203, prime_sixtyOneBG_3308602481257442008417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057652 : Nat.totient 72118279930272158718193057652 = 36059122194689975661337614656 := by
  rw [← show ((([(2, 2), (2030009, 1), (4884810143, 1), (1818191891099, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_2030009, prime_sixtyOneBG_4884810143, prime_sixtyOneBG_1818191891099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057653 : Nat.totient 72118279930272158718193057653 = 47054460515138597978816194560 := by
  rw [← show ((([(3, 1), (47, 1), (32713, 1), (15635287580657343528641, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_47, prime_sixtyOneBG_32713, prime_sixtyOneBG_15635287580657343528641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057654 : Nat.totient 72118279930272158718193057654 = 36030998685939912967211266048 := by
  rw [← show ((([(2, 1), (1997, 1), (6029, 1), (8783, 1), (9370337, 1), (36390994349, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_1997, prime_sixtyOneBG_6029, prime_sixtyOneBG_8783, prime_sixtyOneBG_9370337, prime_sixtyOneBG_36390994349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057655 : Nat.totient 72118279930272158718193057655 = 57694623944217726974554446120 := by
  rw [← show ((([(5, 1), (14423655986054431743638611531, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_5, prime_sixtyOneBG_14423655986054431743638611531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057656 : Nat.totient 72118279930272158718193057656 = 22306672203429541141811036160 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (71, 1), (5995009, 1), (415276168317976963, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_17, prime_sixtyOneBG_71, prime_sixtyOneBG_5995009, prime_sixtyOneBG_415276168317976963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057657 : Nat.totient 72118279930272158718193057657 = 61801747525976498360571456000 := by
  rw [← show ((([(7, 1), (4441, 1), (36945031, 1), (62792895760045681, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_7, prime_sixtyOneBG_4441, prime_sixtyOneBG_36945031, prime_sixtyOneBG_62792895760045681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057658 : Nat.totient 72118279930272158718193057658 = 33585307675142285607514295040 := by
  rw [← show ((([(2, 1), (19, 1), (67, 1), (509, 1), (99669893077, 1), (558348284261, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_19, prime_sixtyOneBG_67, prime_sixtyOneBG_509, prime_sixtyOneBG_99669893077, prime_sixtyOneBG_558348284261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057659 : Nat.totient 72118279930272158718193057659 = 43708048442589187101935181600 := by
  rw [← show ((([(3, 6), (11, 1), (8993425605471026152661561, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_11, prime_sixtyOneBG_8993425605471026152661561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057660 : Nat.totient 72118279930272158718193057660 = 28847301319077388468499865984 := by
  rw [← show ((([(2, 2), (5, 1), (2707897, 1), (1331628934377344461739, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_2707897, prime_sixtyOneBG_1331628934377344461739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057661 : Nat.totient 72118279930272158718193057661 = 72090576487199764901469829440 := by
  rw [← show ((([(2677, 1), (94427, 1), (3922995239, 1), (72724880381, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2677, prime_sixtyOneBG_94427, prime_sixtyOneBG_3922995239, prime_sixtyOneBG_72724880381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057662 : Nat.totient 72118279930272158718193057662 = 21814134216181955522971058688 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (59, 1), (1716310382939, 1), (9130675655729, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_13, prime_sixtyOneBG_59, prime_sixtyOneBG_1716310382939, prime_sixtyOneBG_9130675655729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057663 : Nat.totient 72118279930272158718193057663 = 72043981884013257114572184600 := by
  rw [← show ((([(971, 1), (2784491, 1), (26673518767235154583, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_971, prime_sixtyOneBG_2784491, prime_sixtyOneBG_26673518767235154583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057664 : Nat.totient 72118279930272158718193057664 = 30507129026155048390825328640 := by
  rw [← show ((([(2, 7), (7, 1), (79, 1), (3229, 1), (1902779, 1), (165826473217481, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_7, prime_sixtyOneBG_79, prime_sixtyOneBG_3229, prime_sixtyOneBG_1902779, prime_sixtyOneBG_165826473217481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057665 : Nat.totient 72118279930272158718193057665 = 38370420515397393948343230720 := by
  rw [← show ((([(3, 1), (5, 1), (461, 1), (4159, 1), (2507634609252292199189, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_5, prime_sixtyOneBG_461, prime_sixtyOneBG_4159, prime_sixtyOneBG_2507634609252292199189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057666 : Nat.totient 72118279930272158718193057666 = 36040171451762055884759722000 := by
  rw [← show ((([(2, 1), (1901, 1), (17306259263, 1), (1096049181006491, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_1901, prime_sixtyOneBG_17306259263, prime_sixtyOneBG_1096049181006491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057667 : Nat.totient 72118279930272158718193057667 = 72117703448068624594383528000 := by
  rw [← show ((([(125101, 1), (41089200631, 1), (14029974650057, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_125101, prime_sixtyOneBG_41089200631, prime_sixtyOneBG_14029974650057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057668 : Nat.totient 72118279930272158718193057668 = 24038859314543788963154301120 := by
  rw [← show ((([(2, 2), (3, 2), (42373, 1), (47277406688661909128581, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_42373, prime_sixtyOneBG_47277406688661909128581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057669 : Nat.totient 72118279930272158718193057669 = 70441081960449886377849843840 := by
  rw [← show ((([(43, 1), (2548877, 1), (68192419, 1), (9649213803641, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_43, prime_sixtyOneBG_2548877, prime_sixtyOneBG_68192419, prime_sixtyOneBG_9649213803641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057670 : Nat.totient 72118279930272158718193057670 = 26224803990203563699614937600 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (1045841, 1), (626883748714037608517, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_11, prime_sixtyOneBG_1045841, prime_sixtyOneBG_626883748714037608517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057671 : Nat.totient 72118279930272158718193057671 = 41189322920181667852446540000 := by
  rw [← show ((([(3, 1), (7, 1), (1951, 1), (1678163671, 1), (1048900954470931, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_7, prime_sixtyOneBG_1951, prime_sixtyOneBG_1678163671, prime_sixtyOneBG_1048900954470931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057672 : Nat.totient 72118279930272158718193057672 = 36059139965136079359096528832 := by
  rw [← show ((([(2, 3), (9014784991284019839774132209, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_9014784991284019839774132209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057673 : Nat.totient 72118279930272158718193057673 = 64811489967560408750751744000 := by
  rw [← show ((([(17, 1), (23, 1), (577, 1), (117779, 1), (193601, 1), (14019009516341, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_17, prime_sixtyOneBG_23, prime_sixtyOneBG_577, prime_sixtyOneBG_117779, prime_sixtyOneBG_193601, prime_sixtyOneBG_14019009516341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057674 : Nat.totient 72118279930272158718193057674 = 24039426643394053695021283568 := by
  rw [← show ((([(2, 1), (3, 1), (801378110333, 1), (14998804143424163, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_801378110333, prime_sixtyOneBG_14998804143424163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057675 : Nat.totient 72118279930272158718193057675 = 53256575948508671053434873120 := by
  rw [← show ((([(5, 2), (13, 1), (221902399785452796055978639, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_5, prime_sixtyOneBG_13, prime_sixtyOneBG_221902399785452796055978639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057676 : Nat.totient 72118279930272158718193057676 = 35754194990386417007225984000 := by
  rw [← show ((([(2, 2), (131, 1), (2309, 1), (4139, 1), (6449, 1), (2233069998008951, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_131, prime_sixtyOneBG_2309, prime_sixtyOneBG_4139, prime_sixtyOneBG_6449, prime_sixtyOneBG_2233069998008951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057677 : Nat.totient 72118279930272158718193057677 = 45540621993101683752750378240 := by
  rw [← show ((([(3, 2), (19, 1), (5881, 1), (2240723, 1), (32004415360578949, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_19, prime_sixtyOneBG_5881, prime_sixtyOneBG_2240723, prime_sixtyOneBG_32004415360578949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057678 : Nat.totient 72118279930272158718193057678 = 30907819295881099876203505920 := by
  rw [← show ((([(2, 1), (7, 1), (2066293, 1), (19287079621, 1), (129258450809, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_7, prime_sixtyOneBG_2066293, prime_sixtyOneBG_19287079621, prime_sixtyOneBG_129258450809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057679 : Nat.totient 72118279930272158718193057679 = 67385266475924828156471424000 := by
  rw [← show ((([(29, 1), (31, 1), (104524261, 1), (767482643058003361, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_29, prime_sixtyOneBG_31, prime_sixtyOneBG_104524261, prime_sixtyOneBG_767482643058003361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057680 : Nat.totient 72118279930272158718193057680 = 19231541314735802094196806144 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (6337336267579, 1), (47416267711733, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_5, prime_sixtyOneBG_6337336267579, prime_sixtyOneBG_47416267711733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057681 : Nat.totient 72118279930272158718193057681 = 63126785091416953468260188160 := by
  rw [← show ((([(11, 2), (37, 1), (97, 1), (11329, 1), (461233, 1), (31781513998357, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_11, prime_sixtyOneBG_37, prime_sixtyOneBG_97, prime_sixtyOneBG_11329, prime_sixtyOneBG_461233, prime_sixtyOneBG_31781513998357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057682 : Nat.totient 72118279930272158718193057682 = 36020420380495854223906065600 := by
  rw [← show ((([(2, 1), (1831, 1), (3779, 1), (3797, 1), (513164291, 1), (2674564667, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_1831, prime_sixtyOneBG_3779, prime_sixtyOneBG_3797, prime_sixtyOneBG_513164291, prime_sixtyOneBG_2674564667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057683 : Nat.totient 72118279930272158718193057683 = 46782151824411329087308861440 := by
  rw [← show ((([(3, 1), (41, 1), (379, 1), (165883, 1), (32781097, 1), (284495679049, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_41, prime_sixtyOneBG_379, prime_sixtyOneBG_165883, prime_sixtyOneBG_32781097, prime_sixtyOneBG_284495679049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057684 : Nat.totient 72118279930272158718193057684 = 36059120493935517747196428000 := by
  rw [← show ((([(2, 2), (2028391, 1), (21286541, 1), (417569335188191, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_2028391, prime_sixtyOneBG_21286541, prime_sixtyOneBG_417569335188191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057685 : Nat.totient 72118279930272158718193057685 = 49452534809329480263903810960 := by
  rw [← show ((([(5, 1), (7, 1), (2060522283722061677662658791, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_5, prime_sixtyOneBG_7, prime_sixtyOneBG_2060522283722061677662658791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057686 : Nat.totient 72118279930272158718193057686 = 23926935150659284125275013120 := by
  rw [← show ((([(2, 1), (3, 3), (353, 1), (599, 1), (6133, 1), (50891, 1), (20236533621649, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_353, prime_sixtyOneBG_599, prime_sixtyOneBG_6133, prime_sixtyOneBG_50891, prime_sixtyOneBG_20236533621649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057687 : Nat.totient 72118279930272158718193057687 = 72118279930272158718193057686 := by
  rw [← show ((([(72118279930272158718193057687, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_72118279930272158718193057687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057688 : Nat.totient 72118279930272158718193057688 = 33285359967817919408396795808 := by
  rw [← show ((([(2, 3), (13, 1), (693444999329539987674933247, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_13, prime_sixtyOneBG_693444999329539987674933247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057689 : Nat.totient 72118279930272158718193057689 = 47163026634758048246077976832 := by
  rw [← show ((([(3, 1), (53, 1), (5437, 1), (19465079, 1), (4285808205231877, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_53, prime_sixtyOneBG_5437, prime_sixtyOneBG_19465079, prime_sixtyOneBG_4285808205231877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057690 : Nat.totient 72118279930272158718193057690 = 27150411267867165635084445184 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (424225176060424463048194457, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_17, prime_sixtyOneBG_424225176060424463048194457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057691 : Nat.totient 72118279930272158718193057691 = 72118279930208202570929595000 := by
  rw [← show ((([(1127640650501, 1), (63955019622812191, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_1127640650501, prime_sixtyOneBG_63955019622812191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057692 : Nat.totient 72118279930272158718193057692 = 18715250821484841760509166080 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (11, 1), (1117, 1), (11776498549, 1), (847629362743, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_7, prime_sixtyOneBG_11, prime_sixtyOneBG_1117, prime_sixtyOneBG_11776498549, prime_sixtyOneBG_847629362743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057693 : Nat.totient 72118279930272158718193057693 = 72118279276668873688058812060 := by
  rw [← show ((([(110339531, 1), (653603285030023906103, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_110339531, prime_sixtyOneBG_653603285030023906103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057694 : Nat.totient 72118279930272158718193057694 = 36038705434470392563100126208 := by
  rw [← show ((([(2, 1), (2777, 1), (8243, 1), (11717, 1), (57852229, 1), (2323901189, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_2777, prime_sixtyOneBG_8243, prime_sixtyOneBG_11717, prime_sixtyOneBG_57852229, prime_sixtyOneBG_2323901189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057695 : Nat.totient 72118279930272158718193057695 = 38463082629478484649702964080 := by
  rw [← show ((([(3, 2), (5, 1), (1602628442894936860404290171, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_3, prime_sixtyOneBG_5, prime_sixtyOneBG_1602628442894936860404290171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057696 : Nat.totient 72118279930272158718193057696 = 32676016993546808410897294080 := by
  rw [← show ((([(2, 5), (19, 1), (23, 1), (1433068976011, 1), (3598709997979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_19, prime_sixtyOneBG_23, prime_sixtyOneBG_1433068976011, prime_sixtyOneBG_3598709997979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057697 : Nat.totient 72118279930272158718193057697 = 71513716366706428528425768960 := by
  rw [← show ((([(137, 1), (919, 1), (328781, 1), (2146043, 1), (811828231153, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_137, prime_sixtyOneBG_919, prime_sixtyOneBG_328781, prime_sixtyOneBG_2146043, prime_sixtyOneBG_811828231153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057698 : Nat.totient 72118279930272158718193057698 = 23925368739280123198092517200 := by
  rw [← show ((([(2, 1), (3, 1), (211, 1), (188431, 1), (302314725176206943063, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_3, prime_sixtyOneBG_211, prime_sixtyOneBG_188431, prime_sixtyOneBG_302314725176206943063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057699 : Nat.totient 72118279930272158718193057699 = 61215484091139933051382590528 := by
  rw [← show ((([(7, 1), (103, 1), (1895273, 1), (52776224627660953403, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_7, prime_sixtyOneBG_103, prime_sixtyOneBG_1895273, prime_sixtyOneBG_52776224627660953403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyOneBG_72118279930272158718193057700 : Nat.totient 72118279930272158718193057700 = 28231142816410239212211694080 := by
  rw [← show ((([(2, 2), (5, 2), (47, 1), (11909, 1), (1094773, 1), (1176923213049863, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272158718193057700 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyOneBG_2, prime_sixtyOneBG_5, prime_sixtyOneBG_47, prime_sixtyOneBG_11909, prime_sixtyOneBG_1094773, prime_sixtyOneBG_1176923213049863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyOneBG : certifiedKill 1 72118279930272158718193057599 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyOneBG_72118279930272158718193057600, phi_sixtyOneBG_72118279930272158718193057601, phi_sixtyOneBG_72118279930272158718193057602,
    phi_sixtyOneBG_72118279930272158718193057603, phi_sixtyOneBG_72118279930272158718193057604, phi_sixtyOneBG_72118279930272158718193057605,
    phi_sixtyOneBG_72118279930272158718193057606, phi_sixtyOneBG_72118279930272158718193057607, phi_sixtyOneBG_72118279930272158718193057608,
    phi_sixtyOneBG_72118279930272158718193057609, phi_sixtyOneBG_72118279930272158718193057610, phi_sixtyOneBG_72118279930272158718193057611,
    phi_sixtyOneBG_72118279930272158718193057612, phi_sixtyOneBG_72118279930272158718193057613, phi_sixtyOneBG_72118279930272158718193057614,
    phi_sixtyOneBG_72118279930272158718193057615, phi_sixtyOneBG_72118279930272158718193057616, phi_sixtyOneBG_72118279930272158718193057617,
    phi_sixtyOneBG_72118279930272158718193057618, phi_sixtyOneBG_72118279930272158718193057619, phi_sixtyOneBG_72118279930272158718193057620,
    phi_sixtyOneBG_72118279930272158718193057621, phi_sixtyOneBG_72118279930272158718193057622, phi_sixtyOneBG_72118279930272158718193057623,
    phi_sixtyOneBG_72118279930272158718193057624, phi_sixtyOneBG_72118279930272158718193057625, phi_sixtyOneBG_72118279930272158718193057626,
    phi_sixtyOneBG_72118279930272158718193057627, phi_sixtyOneBG_72118279930272158718193057628, phi_sixtyOneBG_72118279930272158718193057629,
    phi_sixtyOneBG_72118279930272158718193057630, phi_sixtyOneBG_72118279930272158718193057631, phi_sixtyOneBG_72118279930272158718193057632,
    phi_sixtyOneBG_72118279930272158718193057633, phi_sixtyOneBG_72118279930272158718193057634, phi_sixtyOneBG_72118279930272158718193057635,
    phi_sixtyOneBG_72118279930272158718193057636, phi_sixtyOneBG_72118279930272158718193057637, phi_sixtyOneBG_72118279930272158718193057638,
    phi_sixtyOneBG_72118279930272158718193057639, phi_sixtyOneBG_72118279930272158718193057640, phi_sixtyOneBG_72118279930272158718193057641,
    phi_sixtyOneBG_72118279930272158718193057642, phi_sixtyOneBG_72118279930272158718193057643, phi_sixtyOneBG_72118279930272158718193057644,
    phi_sixtyOneBG_72118279930272158718193057645, phi_sixtyOneBG_72118279930272158718193057646, phi_sixtyOneBG_72118279930272158718193057647,
    phi_sixtyOneBG_72118279930272158718193057648, phi_sixtyOneBG_72118279930272158718193057649, phi_sixtyOneBG_72118279930272158718193057650,
    phi_sixtyOneBG_72118279930272158718193057651, phi_sixtyOneBG_72118279930272158718193057652, phi_sixtyOneBG_72118279930272158718193057653,
    phi_sixtyOneBG_72118279930272158718193057654, phi_sixtyOneBG_72118279930272158718193057655, phi_sixtyOneBG_72118279930272158718193057656,
    phi_sixtyOneBG_72118279930272158718193057657, phi_sixtyOneBG_72118279930272158718193057658, phi_sixtyOneBG_72118279930272158718193057659,
    phi_sixtyOneBG_72118279930272158718193057660, phi_sixtyOneBG_72118279930272158718193057661, phi_sixtyOneBG_72118279930272158718193057662,
    phi_sixtyOneBG_72118279930272158718193057663, phi_sixtyOneBG_72118279930272158718193057664, phi_sixtyOneBG_72118279930272158718193057665,
    phi_sixtyOneBG_72118279930272158718193057666, phi_sixtyOneBG_72118279930272158718193057667, phi_sixtyOneBG_72118279930272158718193057668,
    phi_sixtyOneBG_72118279930272158718193057669, phi_sixtyOneBG_72118279930272158718193057670, phi_sixtyOneBG_72118279930272158718193057671,
    phi_sixtyOneBG_72118279930272158718193057672, phi_sixtyOneBG_72118279930272158718193057673, phi_sixtyOneBG_72118279930272158718193057674,
    phi_sixtyOneBG_72118279930272158718193057675, phi_sixtyOneBG_72118279930272158718193057676, phi_sixtyOneBG_72118279930272158718193057677,
    phi_sixtyOneBG_72118279930272158718193057678, phi_sixtyOneBG_72118279930272158718193057679, phi_sixtyOneBG_72118279930272158718193057680,
    phi_sixtyOneBG_72118279930272158718193057681, phi_sixtyOneBG_72118279930272158718193057682, phi_sixtyOneBG_72118279930272158718193057683,
    phi_sixtyOneBG_72118279930272158718193057684, phi_sixtyOneBG_72118279930272158718193057685, phi_sixtyOneBG_72118279930272158718193057686,
    phi_sixtyOneBG_72118279930272158718193057687, phi_sixtyOneBG_72118279930272158718193057688, phi_sixtyOneBG_72118279930272158718193057689,
    phi_sixtyOneBG_72118279930272158718193057690, phi_sixtyOneBG_72118279930272158718193057691, phi_sixtyOneBG_72118279930272158718193057692,
    phi_sixtyOneBG_72118279930272158718193057693, phi_sixtyOneBG_72118279930272158718193057694, phi_sixtyOneBG_72118279930272158718193057695,
    phi_sixtyOneBG_72118279930272158718193057696, phi_sixtyOneBG_72118279930272158718193057697, phi_sixtyOneBG_72118279930272158718193057698,
    phi_sixtyOneBG_72118279930272158718193057699, phi_sixtyOneBG_72118279930272158718193057700]

end TotientTailPeriodKiller
end Erdos249257
