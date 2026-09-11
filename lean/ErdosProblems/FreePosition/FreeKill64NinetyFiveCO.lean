import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyFiveCOFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyFiveCOFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyFiveCOFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyFiveCOFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyFiveCOFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyFiveCOFastPow a n * ninetyFiveCOFastPow a n * a else ninetyFiveCOFastPow a n * ninetyFiveCOFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyFiveCO_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyFiveCO_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyFiveCO_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyFiveCO_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyFiveCO_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyFiveCO_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyFiveCO_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyFiveCO_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyFiveCO_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyFiveCO_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyFiveCO_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyFiveCO_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyFiveCO_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyFiveCO_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyFiveCO_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyFiveCO_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyFiveCO_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyFiveCO_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyFiveCO_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyFiveCO_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyFiveCO_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyFiveCO_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyFiveCO_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyFiveCO_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyFiveCO_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyFiveCO_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyFiveCO_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyFiveCO_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyFiveCO_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyFiveCO_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyFiveCO_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyFiveCO_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyFiveCO_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetyFiveCO_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyFiveCO_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyFiveCO_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetyFiveCO_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyFiveCO_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetyFiveCO_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetyFiveCO_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetyFiveCO_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetyFiveCO_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyFiveCO_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyFiveCO_199 : Nat.Prime 199 := by norm_num

private theorem prime_ninetyFiveCO_211 : Nat.Prime 211 := by norm_num

private theorem prime_ninetyFiveCO_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetyFiveCO_227 : Nat.Prime 227 := by norm_num

private theorem prime_ninetyFiveCO_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetyFiveCO_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetyFiveCO_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyFiveCO_241 : Nat.Prime 241 := by norm_num

private theorem prime_ninetyFiveCO_251 : Nat.Prime 251 := by norm_num

private theorem prime_ninetyFiveCO_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetyFiveCO_271 : Nat.Prime 271 := by norm_num

private theorem prime_ninetyFiveCO_277 : Nat.Prime 277 := by norm_num

private theorem prime_ninetyFiveCO_283 : Nat.Prime 283 := by norm_num

private theorem prime_ninetyFiveCO_293 : Nat.Prime 293 := by norm_num

private theorem prime_ninetyFiveCO_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetyFiveCO_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetyFiveCO_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyFiveCO_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetyFiveCO_353 : Nat.Prime 353 := by norm_num

private theorem prime_ninetyFiveCO_373 : Nat.Prime 373 := by norm_num

private theorem prime_ninetyFiveCO_379 : Nat.Prime 379 := by norm_num

private theorem prime_ninetyFiveCO_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetyFiveCO_397 : Nat.Prime 397 := by norm_num

private theorem prime_ninetyFiveCO_409 : Nat.Prime 409 := by norm_num

private theorem prime_ninetyFiveCO_431 : Nat.Prime 431 := by norm_num

private theorem prime_ninetyFiveCO_439 : Nat.Prime 439 := by norm_num

private theorem prime_ninetyFiveCO_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetyFiveCO_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetyFiveCO_457 : Nat.Prime 457 := by norm_num

private theorem prime_ninetyFiveCO_461 : Nat.Prime 461 := by norm_num

private theorem prime_ninetyFiveCO_463 : Nat.Prime 463 := by norm_num

private theorem prime_ninetyFiveCO_491 : Nat.Prime 491 := by norm_num

private theorem prime_ninetyFiveCO_499 : Nat.Prime 499 := by norm_num

private theorem prime_ninetyFiveCO_523 : Nat.Prime 523 := by norm_num

private theorem prime_ninetyFiveCO_557 : Nat.Prime 557 := by norm_num

private theorem prime_ninetyFiveCO_563 : Nat.Prime 563 := by norm_num

private theorem prime_ninetyFiveCO_571 : Nat.Prime 571 := by norm_num

private theorem prime_ninetyFiveCO_577 : Nat.Prime 577 := by norm_num

private theorem prime_ninetyFiveCO_593 : Nat.Prime 593 := by norm_num

private theorem prime_ninetyFiveCO_607 : Nat.Prime 607 := by norm_num

private theorem prime_ninetyFiveCO_619 : Nat.Prime 619 := by norm_num

private theorem prime_ninetyFiveCO_641 : Nat.Prime 641 := by norm_num

private theorem prime_ninetyFiveCO_643 : Nat.Prime 643 := by norm_num

private theorem prime_ninetyFiveCO_647 : Nat.Prime 647 := by norm_num

private theorem prime_ninetyFiveCO_673 : Nat.Prime 673 := by norm_num

private theorem prime_ninetyFiveCO_677 : Nat.Prime 677 := by norm_num

private theorem prime_ninetyFiveCO_683 : Nat.Prime 683 := by norm_num

private theorem prime_ninetyFiveCO_691 : Nat.Prime 691 := by norm_num

private theorem prime_ninetyFiveCO_709 : Nat.Prime 709 := by norm_num

private theorem prime_ninetyFiveCO_743 : Nat.Prime 743 := by norm_num

private theorem prime_ninetyFiveCO_757 : Nat.Prime 757 := by norm_num

private theorem prime_ninetyFiveCO_769 : Nat.Prime 769 := by norm_num

private theorem prime_ninetyFiveCO_773 : Nat.Prime 773 := by norm_num

private theorem prime_ninetyFiveCO_797 : Nat.Prime 797 := by norm_num

private theorem prime_ninetyFiveCO_809 : Nat.Prime 809 := by norm_num

private theorem prime_ninetyFiveCO_823 : Nat.Prime 823 := by norm_num

private theorem prime_ninetyFiveCO_839 : Nat.Prime 839 := by norm_num

private theorem prime_ninetyFiveCO_857 : Nat.Prime 857 := by norm_num

private theorem prime_ninetyFiveCO_877 : Nat.Prime 877 := by norm_num

private theorem prime_ninetyFiveCO_883 : Nat.Prime 883 := by norm_num

private theorem prime_ninetyFiveCO_911 : Nat.Prime 911 := by norm_num

private theorem prime_ninetyFiveCO_919 : Nat.Prime 919 := by norm_num

private theorem prime_ninetyFiveCO_937 : Nat.Prime 937 := by norm_num

private theorem prime_ninetyFiveCO_941 : Nat.Prime 941 := by norm_num

private theorem prime_ninetyFiveCO_967 : Nat.Prime 967 := by norm_num

private theorem prime_ninetyFiveCO_971 : Nat.Prime 971 := by norm_num

private theorem prime_ninetyFiveCO_991 : Nat.Prime 991 := by norm_num

private theorem prime_ninetyFiveCO_997 : Nat.Prime 997 := by norm_num

private theorem prime_ninetyFiveCO_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_ninetyFiveCO_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_ninetyFiveCO_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_ninetyFiveCO_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_ninetyFiveCO_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_ninetyFiveCO_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_ninetyFiveCO_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_ninetyFiveCO_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_ninetyFiveCO_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_ninetyFiveCO_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_ninetyFiveCO_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_ninetyFiveCO_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_ninetyFiveCO_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_ninetyFiveCO_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_ninetyFiveCO_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_ninetyFiveCO_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_ninetyFiveCO_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_ninetyFiveCO_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_ninetyFiveCO_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_ninetyFiveCO_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_ninetyFiveCO_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_ninetyFiveCO_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_ninetyFiveCO_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_ninetyFiveCO_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_ninetyFiveCO_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_ninetyFiveCO_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_ninetyFiveCO_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_ninetyFiveCO_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_ninetyFiveCO_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_ninetyFiveCO_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_ninetyFiveCO_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_ninetyFiveCO_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_ninetyFiveCO_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_ninetyFiveCO_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_ninetyFiveCO_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_ninetyFiveCO_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_ninetyFiveCO_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_ninetyFiveCO_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_ninetyFiveCO_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_ninetyFiveCO_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_ninetyFiveCO_2539 : Nat.Prime 2539 := by norm_num

private theorem prime_ninetyFiveCO_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_ninetyFiveCO_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_ninetyFiveCO_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_ninetyFiveCO_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_ninetyFiveCO_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_ninetyFiveCO_2879 : Nat.Prime 2879 := by norm_num

private theorem prime_ninetyFiveCO_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_ninetyFiveCO_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_ninetyFiveCO_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_ninetyFiveCO_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_ninetyFiveCO_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_ninetyFiveCO_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_ninetyFiveCO_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_ninetyFiveCO_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_ninetyFiveCO_3793 : Nat.Prime 3793 := by norm_num

private theorem prime_ninetyFiveCO_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_ninetyFiveCO_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_ninetyFiveCO_4201 : Nat.Prime 4201 := by norm_num

private theorem prime_ninetyFiveCO_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_ninetyFiveCO_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_ninetyFiveCO_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_ninetyFiveCO_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_ninetyFiveCO_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_ninetyFiveCO_5351 : Nat.Prime 5351 := by norm_num

private theorem prime_ninetyFiveCO_5417 : Nat.Prime 5417 := by norm_num

private theorem prime_ninetyFiveCO_5813 : Nat.Prime 5813 := by norm_num

private theorem prime_ninetyFiveCO_6053 : Nat.Prime 6053 := by norm_num

private theorem prime_ninetyFiveCO_6277 : Nat.Prime 6277 := by norm_num

private theorem prime_ninetyFiveCO_6577 : Nat.Prime 6577 := by norm_num

private theorem prime_ninetyFiveCO_6607 : Nat.Prime 6607 := by norm_num

private theorem prime_ninetyFiveCO_6719 : Nat.Prime 6719 := by norm_num

private theorem prime_ninetyFiveCO_6829 : Nat.Prime 6829 := by norm_num

private theorem prime_ninetyFiveCO_6857 : Nat.Prime 6857 := by norm_num

private theorem prime_ninetyFiveCO_6967 : Nat.Prime 6967 := by norm_num

private theorem prime_ninetyFiveCO_7079 : Nat.Prime 7079 := by norm_num

private theorem prime_ninetyFiveCO_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_ninetyFiveCO_8009 : Nat.Prime 8009 := by norm_num

private theorem prime_ninetyFiveCO_8747 : Nat.Prime 8747 := by norm_num

private theorem prime_ninetyFiveCO_8837 : Nat.Prime 8837 := by norm_num

private theorem prime_ninetyFiveCO_8929 : Nat.Prime 8929 := by norm_num

private theorem prime_ninetyFiveCO_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_ninetyFiveCO_9293 : Nat.Prime 9293 := by norm_num

private theorem prime_ninetyFiveCO_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_ninetyFiveCO_9767 : Nat.Prime 9767 := by norm_num

private theorem prime_ninetyFiveCO_9871 : Nat.Prime 9871 := by norm_num

private theorem prime_ninetyFiveCO_10037 : Nat.Prime 10037 := by norm_num

private theorem prime_ninetyFiveCO_10093 : Nat.Prime 10093 := by norm_num

private theorem prime_ninetyFiveCO_10753 : Nat.Prime 10753 := by norm_num

private theorem prime_ninetyFiveCO_10891 : Nat.Prime 10891 := by norm_num

private theorem prime_ninetyFiveCO_10993 : Nat.Prime 10993 := by norm_num

private theorem prime_ninetyFiveCO_11423 : Nat.Prime 11423 := by norm_num

private theorem prime_ninetyFiveCO_11483 : Nat.Prime 11483 := by norm_num

private theorem prime_ninetyFiveCO_11821 : Nat.Prime 11821 := by norm_num

private theorem prime_ninetyFiveCO_12739 : Nat.Prime 12739 := by norm_num

private theorem prime_ninetyFiveCO_13597 : Nat.Prime 13597 := by norm_num

private theorem prime_ninetyFiveCO_13859 : Nat.Prime 13859 := by norm_num

private theorem prime_ninetyFiveCO_13921 : Nat.Prime 13921 := by norm_num

private theorem prime_ninetyFiveCO_15383 : Nat.Prime 15383 := by norm_num

private theorem prime_ninetyFiveCO_15797 : Nat.Prime 15797 := by norm_num

private theorem prime_ninetyFiveCO_15809 : Nat.Prime 15809 := by norm_num

private theorem prime_ninetyFiveCO_15889 : Nat.Prime 15889 := by norm_num

private theorem prime_ninetyFiveCO_18047 : Nat.Prime 18047 := by norm_num

private theorem prime_ninetyFiveCO_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_ninetyFiveCO_19541 : Nat.Prime 19541 := by norm_num

private theorem prime_ninetyFiveCO_19543 : Nat.Prime 19543 := by norm_num

private theorem prime_ninetyFiveCO_19697 : Nat.Prime 19697 := by norm_num

private theorem prime_ninetyFiveCO_19889 : Nat.Prime 19889 := by norm_num

private theorem prime_ninetyFiveCO_20563 : Nat.Prime 20563 := by norm_num

private theorem prime_ninetyFiveCO_21157 : Nat.Prime 21157 := by norm_num

private theorem prime_ninetyFiveCO_21341 : Nat.Prime 21341 := by norm_num

private theorem prime_ninetyFiveCO_21929 : Nat.Prime 21929 := by norm_num

private theorem prime_ninetyFiveCO_22409 : Nat.Prime 22409 := by norm_num

private theorem prime_ninetyFiveCO_22669 : Nat.Prime 22669 := by norm_num

private theorem prime_ninetyFiveCO_23417 : Nat.Prime 23417 := by norm_num

private theorem prime_ninetyFiveCO_24019 : Nat.Prime 24019 := by norm_num

private theorem prime_ninetyFiveCO_26669 : Nat.Prime 26669 := by norm_num

private theorem prime_ninetyFiveCO_28607 : Nat.Prime 28607 := by norm_num

private theorem prime_ninetyFiveCO_29339 : Nat.Prime 29339 := by norm_num

private theorem prime_ninetyFiveCO_30509 : Nat.Prime 30509 := by norm_num

private theorem prime_ninetyFiveCO_30643 : Nat.Prime 30643 := by norm_num

private theorem prime_ninetyFiveCO_32983 : Nat.Prime 32983 := by norm_num

private theorem prime_ninetyFiveCO_34649 : Nat.Prime 34649 := by norm_num

private theorem prime_ninetyFiveCO_36389 : Nat.Prime 36389 := by norm_num

private theorem prime_ninetyFiveCO_36479 : Nat.Prime 36479 := by norm_num

private theorem prime_ninetyFiveCO_36871 : Nat.Prime 36871 := by norm_num

private theorem prime_ninetyFiveCO_37799 : Nat.Prime 37799 := by norm_num

private theorem prime_ninetyFiveCO_37831 : Nat.Prime 37831 := by norm_num

private theorem prime_ninetyFiveCO_40529 : Nat.Prime 40529 := by norm_num

private theorem prime_ninetyFiveCO_40787 : Nat.Prime 40787 := by norm_num

private theorem prime_ninetyFiveCO_41539 : Nat.Prime 41539 := by norm_num

private theorem prime_ninetyFiveCO_41953 : Nat.Prime 41953 := by norm_num

private theorem prime_ninetyFiveCO_42181 : Nat.Prime 42181 := by norm_num

private theorem prime_ninetyFiveCO_42727 : Nat.Prime 42727 := by norm_num

private theorem prime_ninetyFiveCO_44537 : Nat.Prime 44537 := by norm_num

private theorem prime_ninetyFiveCO_44623 : Nat.Prime 44623 := by norm_num

private theorem prime_ninetyFiveCO_44971 : Nat.Prime 44971 := by norm_num

private theorem prime_ninetyFiveCO_45329 : Nat.Prime 45329 := by norm_num

private theorem prime_ninetyFiveCO_47533 : Nat.Prime 47533 := by norm_num

private theorem prime_ninetyFiveCO_50387 : Nat.Prime 50387 := by norm_num

private theorem prime_ninetyFiveCO_50753 : Nat.Prime 50753 := by norm_num

private theorem prime_ninetyFiveCO_53077 : Nat.Prime 53077 := by norm_num

private theorem prime_ninetyFiveCO_53887 : Nat.Prime 53887 := by norm_num

private theorem prime_ninetyFiveCO_58199 : Nat.Prime 58199 := by norm_num

private theorem prime_ninetyFiveCO_58727 : Nat.Prime 58727 := by norm_num

private theorem prime_ninetyFiveCO_60331 : Nat.Prime 60331 := by norm_num

private theorem prime_ninetyFiveCO_60427 : Nat.Prime 60427 := by norm_num

private theorem prime_ninetyFiveCO_60689 : Nat.Prime 60689 := by norm_num

private theorem prime_ninetyFiveCO_65563 : Nat.Prime 65563 := by norm_num

private theorem prime_ninetyFiveCO_70619 : Nat.Prime 70619 := by norm_num

private theorem prime_ninetyFiveCO_72647 : Nat.Prime 72647 := by norm_num

private theorem prime_ninetyFiveCO_74887 : Nat.Prime 74887 := by norm_num

private theorem prime_ninetyFiveCO_75709 : Nat.Prime 75709 := by norm_num

private theorem prime_ninetyFiveCO_80831 : Nat.Prime 80831 := by norm_num

private theorem prime_ninetyFiveCO_83641 : Nat.Prime 83641 := by norm_num

private theorem prime_ninetyFiveCO_88667 : Nat.Prime 88667 := by norm_num

private theorem prime_ninetyFiveCO_89657 : Nat.Prime 89657 := by norm_num

private theorem prime_ninetyFiveCO_89833 : Nat.Prime 89833 := by norm_num

private theorem prime_ninetyFiveCO_100193 : Nat.Prime 100193 := by norm_num

private theorem prime_ninetyFiveCO_109037 : Nat.Prime 109037 := by norm_num

private theorem prime_ninetyFiveCO_112643 : Nat.Prime 112643 := by norm_num

private theorem prime_ninetyFiveCO_114547 : Nat.Prime 114547 := by norm_num

private theorem prime_ninetyFiveCO_125471 : Nat.Prime 125471 := by norm_num

private theorem prime_ninetyFiveCO_125551 : Nat.Prime 125551 := by norm_num

private theorem prime_ninetyFiveCO_128563 : Nat.Prime 128563 := by norm_num

private theorem prime_ninetyFiveCO_132679 : Nat.Prime 132679 := by norm_num

private theorem prime_ninetyFiveCO_134153 : Nat.Prime 134153 := by norm_num

private theorem prime_ninetyFiveCO_137437 : Nat.Prime 137437 := by norm_num

private theorem prime_ninetyFiveCO_138181 : Nat.Prime 138181 := by norm_num

private theorem prime_ninetyFiveCO_141101 : Nat.Prime 141101 := by norm_num

private theorem prime_ninetyFiveCO_143971 : Nat.Prime 143971 := by norm_num

private theorem prime_ninetyFiveCO_144941 : Nat.Prime 144941 := by norm_num

private theorem prime_ninetyFiveCO_149197 : Nat.Prime 149197 := by norm_num

private theorem prime_ninetyFiveCO_154267 : Nat.Prime 154267 := by norm_num

private theorem prime_ninetyFiveCO_156241 : Nat.Prime 156241 := by norm_num

private theorem prime_ninetyFiveCO_157897 : Nat.Prime 157897 := by norm_num

private theorem prime_ninetyFiveCO_161093 : Nat.Prime 161093 := by norm_num

private theorem prime_ninetyFiveCO_167107 : Nat.Prime 167107 := by norm_num

private theorem prime_ninetyFiveCO_168977 : Nat.Prime 168977 := by norm_num

private theorem prime_ninetyFiveCO_170347 : Nat.Prime 170347 := by norm_num

private theorem prime_ninetyFiveCO_175993 : Nat.Prime 175993 := by norm_num

private theorem prime_ninetyFiveCO_176713 : Nat.Prime 176713 := by norm_num

private theorem prime_ninetyFiveCO_180749 : Nat.Prime 180749 := by norm_num

private theorem prime_ninetyFiveCO_186247 : Nat.Prime 186247 := by norm_num

private theorem prime_ninetyFiveCO_205357 : Nat.Prime 205357 := by norm_num

private theorem prime_ninetyFiveCO_205963 : Nat.Prime 205963 := by norm_num

private theorem prime_ninetyFiveCO_209707 : Nat.Prime 209707 := by norm_num

private theorem prime_ninetyFiveCO_210809 : Nat.Prime 210809 := by norm_num

private theorem prime_ninetyFiveCO_219071 : Nat.Prime 219071 := by norm_num

private theorem prime_ninetyFiveCO_229519 : Nat.Prime 229519 := by norm_num

private theorem prime_ninetyFiveCO_240719 : Nat.Prime 240719 := by norm_num

private theorem prime_ninetyFiveCO_243787 : Nat.Prime 243787 := by norm_num

private theorem prime_ninetyFiveCO_276007 : Nat.Prime 276007 := by norm_num

private theorem prime_ninetyFiveCO_278269 : Nat.Prime 278269 := by norm_num

private theorem prime_ninetyFiveCO_281849 : Nat.Prime 281849 := by norm_num

private theorem prime_ninetyFiveCO_304477 : Nat.Prime 304477 := by norm_num

private theorem prime_ninetyFiveCO_324449 : Nat.Prime 324449 := by norm_num

private theorem prime_ninetyFiveCO_337013 : Nat.Prime 337013 := by norm_num

private theorem prime_ninetyFiveCO_388931 : Nat.Prime 388931 := by norm_num

private theorem prime_ninetyFiveCO_389591 : Nat.Prime 389591 := by norm_num

private theorem prime_ninetyFiveCO_392737 : Nat.Prime 392737 := by norm_num

private theorem prime_ninetyFiveCO_393797 : Nat.Prime 393797 := by norm_num

private theorem prime_ninetyFiveCO_399937 : Nat.Prime 399937 := by norm_num

private theorem prime_ninetyFiveCO_403057 : Nat.Prime 403057 := by norm_num

private theorem prime_ninetyFiveCO_403703 : Nat.Prime 403703 := by norm_num

private theorem prime_ninetyFiveCO_414283 : Nat.Prime 414283 := by norm_num

private theorem prime_ninetyFiveCO_415409 : Nat.Prime 415409 := by norm_num

private theorem prime_ninetyFiveCO_418637 : Nat.Prime 418637 := by norm_num

private theorem prime_ninetyFiveCO_431219 : Nat.Prime 431219 := by norm_num

private theorem prime_ninetyFiveCO_432499 : Nat.Prime 432499 := by norm_num

private theorem prime_ninetyFiveCO_452533 : Nat.Prime 452533 := by norm_num

private theorem prime_ninetyFiveCO_469753 : Nat.Prime 469753 := by norm_num

private theorem prime_ninetyFiveCO_493369 : Nat.Prime 493369 := by norm_num

private theorem prime_ninetyFiveCO_528403 : Nat.Prime 528403 := by norm_num

private theorem prime_ninetyFiveCO_564533 : Nat.Prime 564533 := by norm_num

private theorem prime_ninetyFiveCO_568523 : Nat.Prime 568523 := by norm_num

private theorem prime_ninetyFiveCO_605309 : Nat.Prime 605309 := by norm_num

private theorem prime_ninetyFiveCO_636653 : Nat.Prime 636653 := by norm_num

private theorem prime_ninetyFiveCO_644143 : Nat.Prime 644143 := by norm_num

private theorem prime_ninetyFiveCO_736679 : Nat.Prime 736679 := by norm_num

private theorem prime_ninetyFiveCO_770837 : Nat.Prime 770837 := by norm_num

private theorem prime_ninetyFiveCO_794063 : Nat.Prime 794063 := by norm_num

private theorem prime_ninetyFiveCO_801683 : Nat.Prime 801683 := by norm_num

private theorem prime_ninetyFiveCO_825029 : Nat.Prime 825029 := by norm_num

private theorem prime_ninetyFiveCO_877567 : Nat.Prime 877567 := by norm_num

private theorem prime_ninetyFiveCO_930737 : Nat.Prime 930737 := by norm_num

private theorem prime_ninetyFiveCO_1033987 : Nat.Prime 1033987 := by norm_num

private theorem prime_ninetyFiveCO_1119221 : Nat.Prime 1119221 := by norm_num

private theorem prime_ninetyFiveCO_1129859 : Nat.Prime 1129859 := by norm_num

private theorem prime_ninetyFiveCO_1219639 : Nat.Prime 1219639 := by norm_num

private theorem prime_ninetyFiveCO_1295321 : Nat.Prime 1295321 := by norm_num

private theorem prime_ninetyFiveCO_1300709 : Nat.Prime 1300709 := by norm_num

private theorem prime_ninetyFiveCO_1342871 : Nat.Prime 1342871 := by norm_num

private theorem prime_ninetyFiveCO_1395659 : Nat.Prime 1395659 := by norm_num

private theorem prime_ninetyFiveCO_1423003 : Nat.Prime 1423003 := by norm_num

private theorem prime_ninetyFiveCO_1466767 : Nat.Prime 1466767 := by norm_num

private theorem prime_ninetyFiveCO_1513453 : Nat.Prime 1513453 := by norm_num

private theorem prime_ninetyFiveCO_1533407 : Nat.Prime 1533407 := by norm_num

private theorem prime_ninetyFiveCO_1543259 : Nat.Prime 1543259 := by norm_num

private theorem prime_ninetyFiveCO_1553567 : Nat.Prime 1553567 := by norm_num

private theorem prime_ninetyFiveCO_1601161 : Nat.Prime 1601161 := by norm_num

private theorem prime_ninetyFiveCO_1641589 : Nat.Prime 1641589 := by norm_num

private theorem prime_ninetyFiveCO_1699543 : Nat.Prime 1699543 := by norm_num

private theorem prime_ninetyFiveCO_1770127 : Nat.Prime 1770127 := by norm_num

private theorem prime_ninetyFiveCO_1796983 : Nat.Prime 1796983 := by norm_num

private theorem prime_ninetyFiveCO_1833751 : Nat.Prime 1833751 := by norm_num

private theorem prime_ninetyFiveCO_1920487 : Nat.Prime 1920487 := by norm_num

private theorem prime_ninetyFiveCO_1937927 : Nat.Prime 1937927 := by norm_num

private theorem prime_ninetyFiveCO_1938637 : Nat.Prime 1938637 := by norm_num

private theorem prime_ninetyFiveCO_2057537 : Nat.Prime 2057537 := by norm_num

private theorem prime_ninetyFiveCO_2141203 : Nat.Prime 2141203 := by norm_num

private theorem prime_ninetyFiveCO_2160127 : Nat.Prime 2160127 := by norm_num

private theorem prime_ninetyFiveCO_2518231 : Nat.Prime 2518231 := by norm_num

private theorem prime_ninetyFiveCO_2573633 : Nat.Prime 2573633 := by norm_num

private theorem prime_ninetyFiveCO_2793859 : Nat.Prime 2793859 := by norm_num

private theorem prime_ninetyFiveCO_2804189 : Nat.Prime 2804189 := by norm_num

private theorem prime_ninetyFiveCO_2988289 : Nat.Prime 2988289 := by norm_num

private theorem prime_ninetyFiveCO_3184969 : Nat.Prime 3184969 := by norm_num

private theorem prime_ninetyFiveCO_3342683 : Nat.Prime 3342683 := by norm_num

private theorem prime_ninetyFiveCO_3366973 : Nat.Prime 3366973 := by norm_num

private theorem prime_ninetyFiveCO_3503293 : Nat.Prime 3503293 := by norm_num

private theorem prime_ninetyFiveCO_3572357 : Nat.Prime 3572357 := by norm_num

private theorem prime_ninetyFiveCO_3724067 : Nat.Prime 3724067 := by norm_num

private theorem prime_ninetyFiveCO_3853669 : Nat.Prime 3853669 := by norm_num

private theorem prime_ninetyFiveCO_3978167 : Nat.Prime 3978167 := by norm_num

private theorem prime_ninetyFiveCO_3994189 : Nat.Prime 3994189 := by norm_num

private theorem prime_ninetyFiveCO_4267631 : Nat.Prime 4267631 := by norm_num

private theorem prime_ninetyFiveCO_4385489 : Nat.Prime 4385489 := by norm_num

private theorem prime_ninetyFiveCO_4632809 : Nat.Prime 4632809 := by norm_num

private theorem prime_ninetyFiveCO_4927207 : Nat.Prime 4927207 := by norm_num

private theorem prime_ninetyFiveCO_5072371 : Nat.Prime 5072371 := by norm_num

private theorem prime_ninetyFiveCO_5472017 : Nat.Prime 5472017 := by norm_num

private theorem prime_ninetyFiveCO_5495051 : Nat.Prime 5495051 := by norm_num

private theorem prime_ninetyFiveCO_5604013 : Nat.Prime 5604013 := by norm_num

private theorem prime_ninetyFiveCO_5800279 : Nat.Prime 5800279 := by norm_num

private theorem prime_ninetyFiveCO_5862679 : Nat.Prime 5862679 := by norm_num

private theorem prime_ninetyFiveCO_5957899 : Nat.Prime 5957899 := by norm_num

private theorem prime_ninetyFiveCO_6004543 : Nat.Prime 6004543 := by norm_num

private theorem prime_ninetyFiveCO_7056941 : Nat.Prime 7056941 := by norm_num

private theorem prime_ninetyFiveCO_7413023 : Nat.Prime 7413023 := by norm_num

private theorem prime_ninetyFiveCO_7775329 : Nat.Prime 7775329 := by norm_num

private theorem prime_ninetyFiveCO_8109701 : Nat.Prime 8109701 := by norm_num

private theorem prime_ninetyFiveCO_8469271 : Nat.Prime 8469271 := by norm_num

private theorem prime_ninetyFiveCO_8661061 : Nat.Prime 8661061 := by norm_num

private theorem prime_ninetyFiveCO_8808211 : Nat.Prime 8808211 := by norm_num

private theorem prime_ninetyFiveCO_9460259 : Nat.Prime 9460259 := by norm_num

private theorem prime_ninetyFiveCO_10007077 : Nat.Prime 10007077 := by norm_num

private theorem prime_ninetyFiveCO_10247399 : Nat.Prime 10247399 := by norm_num

private theorem prime_ninetyFiveCO_11162993 : Nat.Prime 11162993 := by norm_num

private theorem prime_ninetyFiveCO_11643823 : Nat.Prime 11643823 := by norm_num

private theorem prime_ninetyFiveCO_11685031 : Nat.Prime 11685031 := by norm_num

private theorem prime_ninetyFiveCO_11760557 : Nat.Prime 11760557 := by norm_num

private theorem prime_ninetyFiveCO_12224029 : Nat.Prime 12224029 := by norm_num

private theorem prime_ninetyFiveCO_12443791 : Nat.Prime 12443791 := by norm_num

private theorem prime_ninetyFiveCO_13036867 : Nat.Prime 13036867 := by norm_num

private theorem prime_ninetyFiveCO_13411109 : Nat.Prime 13411109 := by norm_num

private theorem prime_ninetyFiveCO_13929121 : Nat.Prime 13929121 := by norm_num

private theorem prime_ninetyFiveCO_14074523 : Nat.Prime 14074523 := by norm_num

private theorem prime_ninetyFiveCO_14427037 : Nat.Prime 14427037 := by norm_num

private theorem prime_ninetyFiveCO_14829869 : Nat.Prime 14829869 := by norm_num

private theorem prime_ninetyFiveCO_16285091 : Nat.Prime 16285091 := by norm_num

private theorem prime_ninetyFiveCO_16679137 : Nat.Prime 16679137 := by norm_num

private theorem prime_ninetyFiveCO_16754939 : Nat.Prime 16754939 := by norm_num

private theorem prime_ninetyFiveCO_17176039 : Nat.Prime 17176039 := by norm_num

private theorem prime_ninetyFiveCO_17186321 : Nat.Prime 17186321 := by norm_num

private theorem prime_ninetyFiveCO_18175757 : Nat.Prime 18175757 := by norm_num

private theorem prime_ninetyFiveCO_18234763 : Nat.Prime 18234763 := by norm_num

private theorem prime_ninetyFiveCO_20081041 : Nat.Prime 20081041 := by norm_num

private theorem prime_ninetyFiveCO_20618963 : Nat.Prime 20618963 := by norm_num

private theorem prime_ninetyFiveCO_20622299 : Nat.Prime 20622299 := by norm_num

private theorem prime_ninetyFiveCO_22597933 : Nat.Prime 22597933 := by norm_num

private theorem prime_ninetyFiveCO_22651093 : Nat.Prime 22651093 := by norm_num

private theorem prime_ninetyFiveCO_26232677 : Nat.Prime 26232677 := by norm_num

private theorem prime_ninetyFiveCO_26597903 : Nat.Prime 26597903 := by norm_num

private theorem prime_ninetyFiveCO_26922977 : Nat.Prime 26922977 := by norm_num

private theorem prime_ninetyFiveCO_28884403 : Nat.Prime 28884403 := by norm_num

private theorem prime_ninetyFiveCO_29191609 : Nat.Prime 29191609 := by norm_num

private theorem prime_ninetyFiveCO_41899643 : Nat.Prime 41899643 := by
  apply lucas_primality 41899643 (2 : ZMod 41899643)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2663, 1), (7867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2663, 1), (7867, 1)] : List FactorBlock).map factorBlockValue).prod) = 41899643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_2663
      · exact prime_ninetyFiveCO_7867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41899643) ^ 20949821 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 41899643) ^ 15734 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 41899643) ^ 5326 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_42320359 : Nat.Prime 42320359 := by
  apply lucas_primality 42320359 (3 : ZMod 42320359)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1489, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1489, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 42320359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_1489
      · exact prime_ninetyFiveCO_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42320359) ^ 21160179 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42320359) ^ 14106786 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42320359) ^ 28422 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42320359) ^ 26802 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_46250221 : Nat.Prime 46250221 := by
  apply lucas_primality 46250221 (6 : ZMod 46250221)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (770837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (770837, 1)] : List FactorBlock).map factorBlockValue).prod) = 46250221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_770837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 46250221) ^ 23125110 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 46250221) ^ 15416740 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 46250221) ^ 9250044 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 46250221) ^ 60 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_46334209 : Nat.Prime 46334209 := by
  apply lucas_primality 46334209 (14 : ZMod 46334209)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (60331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (60331, 1)] : List FactorBlock).map factorBlockValue).prod) = 46334209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_60331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 46334209) ^ 23167104 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 46334209) ^ 15444736 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 46334209) ^ 768 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_46575293 : Nat.Prime 46575293 := by
  apply lucas_primality 46575293 (2 : ZMod 46575293)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11643823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11643823, 1)] : List FactorBlock).map factorBlockValue).prod) = 46575293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11643823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 46575293) ^ 23287646 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 46575293) ^ 4 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_53183401 : Nat.Prime 53183401 := by
  apply lucas_primality 53183401 (11 : ZMod 53183401)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (137, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (137, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 53183401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_137
      · exact prime_ninetyFiveCO_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 53183401) ^ 26591700 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 53183401) ^ 17727800 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 53183401) ^ 10636680 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 53183401) ^ 388200 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 53183401) ^ 82200 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_53242121 : Nat.Prime 53242121 := by
  apply lucas_primality 53242121 (3 : ZMod 53242121)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (251, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (251, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) = 53242121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_251
      · exact prime_ninetyFiveCO_5303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53242121) ^ 26621060 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 53242121) ^ 10648424 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 53242121) ^ 212120 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 53242121) ^ 10040 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_54490297 : Nat.Prime 54490297 := by
  apply lucas_primality 54490297 (5 : ZMod 54490297)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (47, 1), (67, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (47, 1), (67, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) = 54490297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_47
      · exact prime_ninetyFiveCO_67
      · exact prime_ninetyFiveCO_103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54490297) ^ 27245148 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54490297) ^ 18163432 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54490297) ^ 7784328 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54490297) ^ 1159368 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54490297) ^ 813288 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54490297) ^ 529032 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_65225123 : Nat.Prime 65225123 := by
  apply lucas_primality 65225123 (2 : ZMod 65225123)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (168977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (168977, 1)] : List FactorBlock).map factorBlockValue).prod) = 65225123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_193
      · exact prime_ninetyFiveCO_168977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 65225123) ^ 32612561 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65225123) ^ 337954 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65225123) ^ 386 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_66203707 : Nat.Prime 66203707 := by
  apply lucas_primality 66203707 (2 : ZMod 66203707)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (593, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (593, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 66203707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_593
      · exact prime_ninetyFiveCO_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66203707) ^ 33101853 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 66203707) ^ 22067902 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 66203707) ^ 2878422 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 66203707) ^ 111642 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 66203707) ^ 81834 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_80898887 : Nat.Prime 80898887 := by
  apply lucas_primality 80898887 (5 : ZMod 80898887)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (347, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (347, 1), (6857, 1)] : List FactorBlock).map factorBlockValue).prod) = 80898887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_347
      · exact prime_ninetyFiveCO_6857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 80898887) ^ 40449443 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 80898887) ^ 4758758 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 80898887) ^ 233138 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 80898887) ^ 11798 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_91319077 : Nat.Prime 91319077 := by
  apply lucas_primality 91319077 (2 : ZMod 91319077)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (281849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (281849, 1)] : List FactorBlock).map factorBlockValue).prod) = 91319077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_281849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91319077) ^ 45659538 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 91319077) ^ 30439692 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 91319077) ^ 324 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_93410357 : Nat.Prime 93410357 := by
  apply lucas_primality 93410357 (2 : ZMod 93410357)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (138181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (138181, 1)] : List FactorBlock).map factorBlockValue).prod) = 93410357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_138181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93410357) ^ 46705178 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93410357) ^ 7185412 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93410357) ^ 676 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_106965857 : Nat.Prime 106965857 := by
  apply lucas_primality 106965857 (3 : ZMod 106965857)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3342683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3342683, 1)] : List FactorBlock).map factorBlockValue).prod) = 106965857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3342683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 106965857) ^ 53482928 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 106965857) ^ 32 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_114325283 : Nat.Prime 114325283 := by
  apply lucas_primality 114325283 (2 : ZMod 114325283)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1511, 1), (37831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1511, 1), (37831, 1)] : List FactorBlock).map factorBlockValue).prod) = 114325283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_1511
      · exact prime_ninetyFiveCO_37831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 114325283) ^ 57162641 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 114325283) ^ 75662 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 114325283) ^ 3022 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_115838627 : Nat.Prime 115838627 := by
  apply lucas_primality 115838627 (2 : ZMod 115838627)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (2518231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (2518231, 1)] : List FactorBlock).map factorBlockValue).prod) = 115838627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_2518231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115838627) ^ 57919313 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 115838627) ^ 5036462 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 115838627) ^ 46 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_117905581 : Nat.Prime 117905581 := by
  apply lucas_primality 117905581 (6 : ZMod 117905581)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (50387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (50387, 1)] : List FactorBlock).map factorBlockValue).prod) = 117905581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_50387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 117905581) ^ 58952790 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 117905581) ^ 39301860 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 117905581) ^ 23581116 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 117905581) ^ 9069660 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 117905581) ^ 2340 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_122258063 : Nat.Prime 122258063 := by
  apply lucas_primality 122258063 (5 : ZMod 122258063)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (229, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (229, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) = 122258063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_173
      · exact prime_ninetyFiveCO_229
      · exact prime_ninetyFiveCO_1543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 122258063) ^ 61129031 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 122258063) ^ 706694 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 122258063) ^ 533878 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 122258063) ^ 79234 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_130280729 : Nat.Prime 130280729 := by
  apply lucas_primality 130280729 (3 : ZMod 130280729)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (16285091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (16285091, 1)] : List FactorBlock).map factorBlockValue).prod) = 130280729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_16285091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 130280729) ^ 65140364 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 130280729) ^ 8 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_132036193 : Nat.Prime 132036193 := by
  apply lucas_primality 132036193 (15 : ZMod 132036193)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (23, 1), (31, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (23, 1), (31, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 132036193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 132036193) ^ 66018096 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (15 : ZMod 132036193) ^ 44012064 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (15 : ZMod 132036193) ^ 5740704 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (15 : ZMod 132036193) ^ 4259232 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (15 : ZMod 132036193) ^ 205344 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_149325493 : Nat.Prime 149325493 := by
  apply lucas_primality 149325493 (5 : ZMod 149325493)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12443791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12443791, 1)] : List FactorBlock).map factorBlockValue).prod) = 149325493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_12443791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 149325493) ^ 74662746 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 149325493) ^ 49775164 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 149325493) ^ 12 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_161117851 : Nat.Prime 161117851 := by
  apply lucas_primality 161117851 (2 : ZMod 161117851)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31, 1), (34649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31, 1), (34649, 1)] : List FactorBlock).map factorBlockValue).prod) = 161117851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_34649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161117851) ^ 80558925 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 161117851) ^ 53705950 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 161117851) ^ 32223570 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 161117851) ^ 5197350 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 161117851) ^ 4650 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_175414201 : Nat.Prime 175414201 := by
  apply lucas_primality 175414201 (11 : ZMod 175414201)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (13, 1), (43, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (13, 1), (43, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 175414201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 175414201) ^ 87707100 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 175414201) ^ 58471400 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 175414201) ^ 35082840 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 175414201) ^ 13493400 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 175414201) ^ 4079400 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 175414201) ^ 335400 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_202894841 : Nat.Prime 202894841 := by
  apply lucas_primality 202894841 (3 : ZMod 202894841)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (5072371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (5072371, 1)] : List FactorBlock).map factorBlockValue).prod) = 202894841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_5072371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 202894841) ^ 101447420 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 202894841) ^ 40578968 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 202894841) ^ 40 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_209049349 : Nat.Prime 209049349 := by
  apply lucas_primality 209049349 (2 : ZMod 209049349)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2551, 1), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2551, 1), (6829, 1)] : List FactorBlock).map factorBlockValue).prod) = 209049349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_2551
      · exact prime_ninetyFiveCO_6829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 209049349) ^ 104524674 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 209049349) ^ 69683116 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 209049349) ^ 81948 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 209049349) ^ 30612 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_223512803 : Nat.Prime 223512803 := by
  apply lucas_primality 223512803 (2 : ZMod 223512803)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (3853669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (3853669, 1)] : List FactorBlock).map factorBlockValue).prod) = 223512803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_3853669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 223512803) ^ 111756401 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 223512803) ^ 7707338 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 223512803) ^ 58 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_227302807 : Nat.Prime 227302807 := by
  apply lucas_primality 227302807 (3 : ZMod 227302807)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (797, 1), (47533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (797, 1), (47533, 1)] : List FactorBlock).map factorBlockValue).prod) = 227302807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_797
      · exact prime_ninetyFiveCO_47533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 227302807) ^ 113651403 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 227302807) ^ 75767602 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 227302807) ^ 285198 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 227302807) ^ 4782 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_236186339 : Nat.Prime 236186339 := by
  apply lucas_primality 236186339 (2 : ZMod 236186339)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (53, 2), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (53, 2), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) = 236186339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_53
      · exact prime_ninetyFiveCO_2473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 236186339) ^ 118093169 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 236186339) ^ 13893314 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 236186339) ^ 4456346 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 236186339) ^ 95506 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_265036361 : Nat.Prime 265036361 := by
  apply lucas_primality 265036361 (3 : ZMod 265036361)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (31, 1), (9293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (31, 1), (9293, 1)] : List FactorBlock).map factorBlockValue).prod) = 265036361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_9293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 265036361) ^ 132518180 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 265036361) ^ 53007272 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 265036361) ^ 11523320 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 265036361) ^ 8549560 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 265036361) ^ 28520 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_299461597 : Nat.Prime 299461597 := by
  apply lucas_primality 299461597 (5 : ZMod 299461597)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (209707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (209707, 1)] : List FactorBlock).map factorBlockValue).prod) = 299461597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_209707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 299461597) ^ 149730798 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 299461597) ^ 99820532 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 299461597) ^ 42780228 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 299461597) ^ 17615388 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 299461597) ^ 1428 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_310758823 : Nat.Prime 310758823 := by
  apply lucas_primality 310758823 (5 : ZMod 310758823)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (53, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (53, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) = 310758823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_53
      · exact prime_ninetyFiveCO_9871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 310758823) ^ 155379411 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 310758823) ^ 103586274 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 310758823) ^ 28250802 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 310758823) ^ 5863374 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 310758823) ^ 31482 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_367106741 : Nat.Prime 367106741 := by
  apply lucas_primality 367106741 (3 : ZMod 367106741)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 2), (13, 1), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 2), (13, 1), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) = 367106741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_1667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 367106741) ^ 183553370 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 367106741) ^ 73421348 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 367106741) ^ 52443820 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 367106741) ^ 33373340 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 367106741) ^ 28238980 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 367106741) ^ 220220 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_375691271 : Nat.Prime 375691271 := by
  apply lucas_primality 375691271 (7 : ZMod 375691271)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (191, 1), (239, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (191, 1), (239, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 375691271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_191
      · exact prime_ninetyFiveCO_239
      · exact prime_ninetyFiveCO_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 375691271) ^ 187845635 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 375691271) ^ 75138254 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 375691271) ^ 1966970 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 375691271) ^ 1571930 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 375691271) ^ 456490 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_377682883 : Nat.Prime 377682883 := by
  apply lucas_primality 377682883 (7 : ZMod 377682883)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (709, 1), (1889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (709, 1), (1889, 1)] : List FactorBlock).map factorBlockValue).prod) = 377682883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_47
      · exact prime_ninetyFiveCO_709
      · exact prime_ninetyFiveCO_1889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 377682883) ^ 188841441 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 377682883) ^ 125894294 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 377682883) ^ 8035806 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 377682883) ^ 532698 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 377682883) ^ 199938 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_394814669 : Nat.Prime 394814669 := by
  apply lucas_primality 394814669 (2 : ZMod 394814669)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2677, 1), (36871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2677, 1), (36871, 1)] : List FactorBlock).map factorBlockValue).prod) = 394814669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_2677
      · exact prime_ninetyFiveCO_36871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 394814669) ^ 197407334 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 394814669) ^ 147484 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 394814669) ^ 10708 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_543608237 : Nat.Prime 543608237 := by
  apply lucas_primality 543608237 (2 : ZMod 543608237)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (839, 1), (3767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (839, 1), (3767, 1)] : List FactorBlock).map factorBlockValue).prod) = 543608237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_839
      · exact prime_ninetyFiveCO_3767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 543608237) ^ 271804118 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 543608237) ^ 12642052 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 543608237) ^ 647924 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 543608237) ^ 144308 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_592999553 : Nat.Prime 592999553 := by
  apply lucas_primality 592999553 (3 : ZMod 592999553)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (4632809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (4632809, 1)] : List FactorBlock).map factorBlockValue).prod) = 592999553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_4632809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 592999553) ^ 296499776 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 592999553) ^ 128 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_626476481 : Nat.Prime 626476481 := by
  apply lucas_primality 626476481 (6 : ZMod 626476481)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (307, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (307, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 626476481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_307
      · exact prime_ninetyFiveCO_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 626476481) ^ 313238240 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 626476481) ^ 125295296 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 626476481) ^ 89496640 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 626476481) ^ 2040640 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 626476481) ^ 687680 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_684379879 : Nat.Prime 684379879 := by
  apply lucas_primality 684379879 (3 : ZMod 684379879)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (47, 1), (26669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (47, 1), (26669, 1)] : List FactorBlock).map factorBlockValue).prod) = 684379879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_47
      · exact prime_ninetyFiveCO_26669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 684379879) ^ 342189939 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 684379879) ^ 228126626 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 684379879) ^ 97768554 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 684379879) ^ 52644606 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 684379879) ^ 14561274 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 684379879) ^ 25662 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_771539723 : Nat.Prime 771539723 := by
  apply lucas_primality 771539723 (2 : ZMod 771539723)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (41, 1), (324449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (41, 1), (324449, 1)] : List FactorBlock).map factorBlockValue).prod) = 771539723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_324449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 771539723) ^ 385769861 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 771539723) ^ 26604818 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 771539723) ^ 18818042 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 771539723) ^ 2378 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_824886269 : Nat.Prime 824886269 := by
  apply lucas_primality 824886269 (2 : ZMod 824886269)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (439, 1), (469753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (439, 1), (469753, 1)] : List FactorBlock).map factorBlockValue).prod) = 824886269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_439
      · exact prime_ninetyFiveCO_469753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 824886269) ^ 412443134 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 824886269) ^ 1879012 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 824886269) ^ 1756 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_828204583 : Nat.Prime 828204583 := by
  apply lucas_primality 828204583 (5 : ZMod 828204583)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3323, 1), (41539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3323, 1), (41539, 1)] : List FactorBlock).map factorBlockValue).prod) = 828204583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_3323
      · exact prime_ninetyFiveCO_41539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 828204583) ^ 414102291 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 828204583) ^ 276068194 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 828204583) ^ 249234 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 828204583) ^ 19938 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_958172543 : Nat.Prime 958172543 := by
  apply lucas_primality 958172543 (5 : ZMod 958172543)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (11685031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (11685031, 1)] : List FactorBlock).map factorBlockValue).prod) = 958172543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_11685031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 958172543) ^ 479086271 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 958172543) ^ 23370062 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 958172543) ^ 82 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1013178137 : Nat.Prime 1013178137 := by
  apply lucas_primality 1013178137 (3 : ZMod 1013178137)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (1423003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (1423003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013178137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_89
      · exact prime_ninetyFiveCO_1423003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1013178137) ^ 506589068 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013178137) ^ 11384024 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013178137) ^ 712 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1039838509 : Nat.Prime 1039838509 := by
  apply lucas_primality 1039838509 (6 : ZMod 1039838509)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (28884403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (28884403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1039838509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_28884403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1039838509) ^ 519919254 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1039838509) ^ 346612836 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1039838509) ^ 36 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1047579493 : Nat.Prime 1047579493 := by
  apply lucas_primality 1047579493 (5 : ZMod 1047579493)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (181, 1), (6607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (181, 1), (6607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047579493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_73
      · exact prime_ninetyFiveCO_181
      · exact prime_ninetyFiveCO_6607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1047579493) ^ 523789746 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047579493) ^ 349193164 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047579493) ^ 14350404 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047579493) ^ 5787732 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047579493) ^ 158556 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1215968713 : Nat.Prime 1215968713 := by
  apply lucas_primality 1215968713 (5 : ZMod 1215968713)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (1033987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (1033987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1215968713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_1033987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1215968713) ^ 607984356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1215968713) ^ 405322904 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1215968713) ^ 173709816 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1215968713) ^ 1176 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1397258791 : Nat.Prime 1397258791 := by
  apply lucas_primality 1397258791 (3 : ZMod 1397258791)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (46575293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (46575293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1397258791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_46575293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1397258791) ^ 698629395 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1397258791) ^ 465752930 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1397258791) ^ 279451758 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1397258791) ^ 30 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2176334969 : Nat.Prime 2176334969 := by
  apply lucas_primality 2176334969 (3 : ZMod 2176334969)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (37, 1), (432499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (37, 1), (432499, 1)] : List FactorBlock).map factorBlockValue).prod) = 2176334969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_37
      · exact prime_ninetyFiveCO_432499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2176334969) ^ 1088167484 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2176334969) ^ 128019704 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2176334969) ^ 58819864 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2176334969) ^ 5032 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2626542091 : Nat.Prime 2626542091 := by
  apply lucas_primality 2626542091 (2 : ZMod 2626542091)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (227, 1), (128563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (227, 1), (128563, 1)] : List FactorBlock).map factorBlockValue).prod) = 2626542091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_227
      · exact prime_ninetyFiveCO_128563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2626542091) ^ 1313271045 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2626542091) ^ 875514030 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2626542091) ^ 525308418 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2626542091) ^ 11570670 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2626542091) ^ 20430 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2626695233 : Nat.Prime 2626695233 := by
  apply lucas_primality 2626695233 (3 : ZMod 2626695233)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (139, 1), (42181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (139, 1), (42181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2626695233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_139
      · exact prime_ninetyFiveCO_42181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2626695233) ^ 1313347616 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2626695233) ^ 375242176 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2626695233) ^ 18897088 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2626695233) ^ 62272 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2687083573 : Nat.Prime 2687083573 := by
  apply lucas_primality 2687083573 (22 : ZMod 2687083573)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (383, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (383, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2687083573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_73
      · exact prime_ninetyFiveCO_383
      · exact prime_ninetyFiveCO_8009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2687083573) ^ 1343541786 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (22 : ZMod 2687083573) ^ 895694524 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (22 : ZMod 2687083573) ^ 36809364 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (22 : ZMod 2687083573) ^ 7015884 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (22 : ZMod 2687083573) ^ 335508 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2836799947 : Nat.Prime 2836799947 := by
  apply lucas_primality 2836799947 (2 : ZMod 2836799947)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (571, 1), (276007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (571, 1), (276007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2836799947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_571
      · exact prime_ninetyFiveCO_276007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2836799947) ^ 1418399973 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2836799947) ^ 945599982 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2836799947) ^ 4968126 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2836799947) ^ 10278 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3010712879 : Nat.Prime 3010712879 := by
  apply lucas_primality 3010712879 (11 : ZMod 3010712879)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8837, 1), (170347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8837, 1), (170347, 1)] : List FactorBlock).map factorBlockValue).prod) = 3010712879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_8837
      · exact prime_ninetyFiveCO_170347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 3010712879) ^ 1505356439 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 3010712879) ^ 340694 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 3010712879) ^ 17674 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3158370379 : Nat.Prime 3158370379 := by
  apply lucas_primality 3158370379 (2 : ZMod 3158370379)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (997, 1), (175993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (997, 1), (175993, 1)] : List FactorBlock).map factorBlockValue).prod) = 3158370379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_997
      · exact prime_ninetyFiveCO_175993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3158370379) ^ 1579185189 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3158370379) ^ 1052790126 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3158370379) ^ 3167874 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3158370379) ^ 17946 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3209669423 : Nat.Prime 3209669423 := by
  apply lucas_primality 3209669423 (5 : ZMod 3209669423)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1033, 1), (1553567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1033, 1), (1553567, 1)] : List FactorBlock).map factorBlockValue).prod) = 3209669423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_1033
      · exact prime_ninetyFiveCO_1553567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3209669423) ^ 1604834711 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3209669423) ^ 3107134 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3209669423) ^ 2066 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3255225067 : Nat.Prime 3255225067 := by
  apply lucas_primality 3255225067 (26 : ZMod 3255225067)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (971, 1), (186247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (971, 1), (186247, 1)] : List FactorBlock).map factorBlockValue).prod) = 3255225067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_971
      · exact prime_ninetyFiveCO_186247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 3255225067) ^ 1627612533 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3255225067) ^ 1085075022 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3255225067) ^ 3352446 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (26 : ZMod 3255225067) ^ 17478 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3746931709 : Nat.Prime 3746931709 := by
  apply lucas_primality 3746931709 (6 : ZMod 3746931709)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (709, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (709, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 3746931709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_709
      · exact prime_ninetyFiveCO_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3746931709) ^ 1873465854 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746931709) ^ 1248977236 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746931709) ^ 288225516 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746931709) ^ 197206932 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746931709) ^ 5284812 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746931709) ^ 2101476 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_4216457761 : Nat.Prime 4216457761 := by
  apply lucas_primality 4216457761 (7 : ZMod 4216457761)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (769, 1), (11423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (769, 1), (11423, 1)] : List FactorBlock).map factorBlockValue).prod) = 4216457761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_769
      · exact prime_ninetyFiveCO_11423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4216457761) ^ 2108228880 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4216457761) ^ 1405485920 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4216457761) ^ 843291552 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4216457761) ^ 5483040 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 4216457761) ^ 369120 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_4378590521 : Nat.Prime 4378590521 := by
  apply lucas_primality 4378590521 (6 : ZMod 4378590521)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (1877, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (1877, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 4378590521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_1877
      · exact prime_ninetyFiveCO_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4378590521) ^ 2189295260 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4378590521) ^ 875718104 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4378590521) ^ 150985880 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4378590521) ^ 2332760 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4378590521) ^ 2177320 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_4637757143 : Nat.Prime 4637757143 := by
  apply lucas_primality 4637757143 (5 : ZMod 4637757143)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (683, 1), (967, 1), (3511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (683, 1), (967, 1), (3511, 1)] : List FactorBlock).map factorBlockValue).prod) = 4637757143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_683
      · exact prime_ninetyFiveCO_967
      · exact prime_ninetyFiveCO_3511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4637757143) ^ 2318878571 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4637757143) ^ 6790274 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4637757143) ^ 4796026 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4637757143) ^ 1320922 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_6051572759 : Nat.Prime 6051572759 := by
  apply lucas_primality 6051572759 (7 : ZMod 6051572759)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (3572357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (3572357, 1)] : List FactorBlock).map factorBlockValue).prod) = 6051572759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_3572357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6051572759) ^ 3025786379 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6051572759) ^ 864510394 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6051572759) ^ 550142978 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6051572759) ^ 1694 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_8405084533 : Nat.Prime 8405084533 := by
  apply lucas_primality 8405084533 (5 : ZMod 8405084533)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (97, 1), (42727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (97, 1), (42727, 1)] : List FactorBlock).map factorBlockValue).prod) = 8405084533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_97
      · exact prime_ninetyFiveCO_42727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8405084533) ^ 4202542266 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8405084533) ^ 2801694844 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8405084533) ^ 646544964 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8405084533) ^ 86650356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8405084533) ^ 196716 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_10082426941 : Nat.Prime 10082426941 := by
  apply lucas_primality 10082426941 (10 : ZMod 10082426941)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (163, 1), (114547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (163, 1), (114547, 1)] : List FactorBlock).map factorBlockValue).prod) = 10082426941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_163
      · exact prime_ninetyFiveCO_114547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10082426941) ^ 5041213470 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 10082426941) ^ 3360808980 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 10082426941) ^ 2016485388 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 10082426941) ^ 61855380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 10082426941) ^ 88020 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_11003707877 : Nat.Prime 11003707877 := by
  apply lucas_primality 11003707877 (2 : ZMod 11003707877)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (191, 1), (2057537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (191, 1), (2057537, 1)] : List FactorBlock).map factorBlockValue).prod) = 11003707877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_191
      · exact prime_ninetyFiveCO_2057537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11003707877) ^ 5501853938 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11003707877) ^ 1571958268 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11003707877) ^ 57611036 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11003707877) ^ 5348 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_11124935123 : Nat.Prime 11124935123 := by
  apply lucas_primality 11124935123 (2 : ZMod 11124935123)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (137, 1), (5800279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (137, 1), (5800279, 1)] : List FactorBlock).map factorBlockValue).prod) = 11124935123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_137
      · exact prime_ninetyFiveCO_5800279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11124935123) ^ 5562467561 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11124935123) ^ 1589276446 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11124935123) ^ 81203906 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11124935123) ^ 1918 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_12861235493 : Nat.Prime 12861235493 := by
  apply lucas_primality 12861235493 (2 : ZMod 12861235493)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (103, 1), (1487, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (103, 1), (1487, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) = 12861235493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_103
      · exact prime_ninetyFiveCO_1487
      · exact prime_ninetyFiveCO_2999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12861235493) ^ 6430617746 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12861235493) ^ 1837319356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12861235493) ^ 124866364 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12861235493) ^ 8649116 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12861235493) ^ 4288508 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_13818559351 : Nat.Prime 13818559351 := by
  apply lucas_primality 13818559351 (3 : ZMod 13818559351)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (4201, 1), (21929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (4201, 1), (21929, 1)] : List FactorBlock).map factorBlockValue).prod) = 13818559351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_4201
      · exact prime_ninetyFiveCO_21929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13818559351) ^ 6909279675 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13818559351) ^ 4606186450 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13818559351) ^ 2763711870 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13818559351) ^ 3289350 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13818559351) ^ 630150 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_14545930913 : Nat.Prime 14545930913 := by
  apply lucas_primality 14545930913 (3 : ZMod 14545930913)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2207, 1), (205963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2207, 1), (205963, 1)] : List FactorBlock).map factorBlockValue).prod) = 14545930913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_2207
      · exact prime_ninetyFiveCO_205963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14545930913) ^ 7272965456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14545930913) ^ 6590816 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14545930913) ^ 70624 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_15759252547 : Nat.Prime 15759252547 := by
  apply lucas_primality 15759252547 (2 : ZMod 15759252547)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2626542091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2626542091, 1)] : List FactorBlock).map factorBlockValue).prod) = 15759252547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_2626542091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15759252547) ^ 7879626273 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15759252547) ^ 5253084182 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15759252547) ^ 6 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_16124392309 : Nat.Prime 16124392309 := by
  apply lucas_primality 16124392309 (2 : ZMod 16124392309)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3449, 1), (389591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3449, 1), (389591, 1)] : List FactorBlock).map factorBlockValue).prod) = 16124392309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_3449
      · exact prime_ninetyFiveCO_389591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16124392309) ^ 8062196154 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 16124392309) ^ 5374797436 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 16124392309) ^ 4675092 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 16124392309) ^ 41388 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_17445604277 : Nat.Prime 17445604277 := by
  apply lucas_primality 17445604277 (2 : ZMod 17445604277)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (193, 1), (22597933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (193, 1), (22597933, 1)] : List FactorBlock).map factorBlockValue).prod) = 17445604277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_193
      · exact prime_ninetyFiveCO_22597933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17445604277) ^ 8722802138 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17445604277) ^ 90391732 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17445604277) ^ 772 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_18167090719 : Nat.Prime 18167090719 := by
  apply lucas_primality 18167090719 (6 : ZMod 18167090719)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3967, 1), (109037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3967, 1), (109037, 1)] : List FactorBlock).map factorBlockValue).prod) = 18167090719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_3967
      · exact prime_ninetyFiveCO_109037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18167090719) ^ 9083545359 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 18167090719) ^ 6055696906 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 18167090719) ^ 2595298674 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 18167090719) ^ 4579554 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 18167090719) ^ 166614 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_19163450861 : Nat.Prime 19163450861 := by
  apply lucas_primality 19163450861 (2 : ZMod 19163450861)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (958172543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (958172543, 1)] : List FactorBlock).map factorBlockValue).prod) = 19163450861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_958172543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19163450861) ^ 9581725430 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19163450861) ^ 3832690172 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19163450861) ^ 20 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_19931343937 : Nat.Prime 19931343937 := by
  apply lucas_primality 19931343937 (5 : ZMod 19931343937)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (14829869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (14829869, 1)] : List FactorBlock).map factorBlockValue).prod) = 19931343937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_14829869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19931343937) ^ 9965671968 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 19931343937) ^ 6643781312 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 19931343937) ^ 2847334848 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 19931343937) ^ 1344 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_20141501117 : Nat.Prime 20141501117 := by
  apply lucas_primality 20141501117 (2 : ZMod 20141501117)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (409, 1), (1119221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (409, 1), (1119221, 1)] : List FactorBlock).map factorBlockValue).prod) = 20141501117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_409
      · exact prime_ninetyFiveCO_1119221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20141501117) ^ 10070750558 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20141501117) ^ 1831045556 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20141501117) ^ 49245724 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20141501117) ^ 17996 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_22595147447 : Nat.Prime 22595147447 := by
  apply lucas_primality 22595147447 (5 : ZMod 22595147447)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (179, 1), (1342871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (179, 1), (1342871, 1)] : List FactorBlock).map factorBlockValue).prod) = 22595147447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_47
      · exact prime_ninetyFiveCO_179
      · exact prime_ninetyFiveCO_1342871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22595147447) ^ 11297573723 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22595147447) ^ 480747818 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22595147447) ^ 126229874 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 22595147447) ^ 16826 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_22753207163 : Nat.Prime 22753207163 := by
  apply lucas_primality 22753207163 (2 : ZMod 22753207163)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (97, 1), (16754939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (97, 1), (16754939, 1)] : List FactorBlock).map factorBlockValue).prod) = 22753207163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_97
      · exact prime_ninetyFiveCO_16754939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22753207163) ^ 11376603581 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22753207163) ^ 3250458166 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22753207163) ^ 234569146 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22753207163) ^ 1358 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_23177027437 : Nat.Prime 23177027437 := by
  apply lucas_primality 23177027437 (2 : ZMod 23177027437)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (36389, 1), (53077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (36389, 1), (53077, 1)] : List FactorBlock).map factorBlockValue).prod) = 23177027437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_36389
      · exact prime_ninetyFiveCO_53077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23177027437) ^ 11588513718 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23177027437) ^ 7725675812 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23177027437) ^ 636924 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23177027437) ^ 436668 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_24553251493 : Nat.Prime 24553251493 := by
  apply lucas_primality 24553251493 (2 : ZMod 24553251493)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (109, 1), (243787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (109, 1), (243787, 1)] : List FactorBlock).map factorBlockValue).prod) = 24553251493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_109
      · exact prime_ninetyFiveCO_243787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24553251493) ^ 12276625746 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24553251493) ^ 8184417164 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24553251493) ^ 3507607356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24553251493) ^ 2232113772 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24553251493) ^ 225259188 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24553251493) ^ 100716 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_27102629507 : Nat.Prime 27102629507 := by
  apply lucas_primality 27102629507 (2 : ZMod 27102629507)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (293, 1), (46250221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (293, 1), (46250221, 1)] : List FactorBlock).map factorBlockValue).prod) = 27102629507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_293
      · exact prime_ninetyFiveCO_46250221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27102629507) ^ 13551314753 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27102629507) ^ 92500442 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27102629507) ^ 586 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_28405277741 : Nat.Prime 28405277741 := by
  apply lucas_primality 28405277741 (2 : ZMod 28405277741)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (202894841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (202894841, 1)] : List FactorBlock).map factorBlockValue).prod) = 28405277741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_202894841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28405277741) ^ 14202638870 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28405277741) ^ 5681055548 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28405277741) ^ 4057896820 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28405277741) ^ 140 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_28649682557 : Nat.Prime 28649682557 := by
  apply lucas_primality 28649682557 (2 : ZMod 28649682557)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (23, 1), (2573633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (23, 1), (2573633, 1)] : List FactorBlock).map factorBlockValue).prod) = 28649682557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_2573633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28649682557) ^ 14324841278 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28649682557) ^ 2604516596 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28649682557) ^ 1245638372 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28649682557) ^ 11132 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_32209312691 : Nat.Prime 32209312691 := by
  apply lucas_primality 32209312691 (2 : ZMod 32209312691)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (97, 1), (397, 1), (83641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (97, 1), (397, 1), (83641, 1)] : List FactorBlock).map factorBlockValue).prod) = 32209312691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_97
      · exact prime_ninetyFiveCO_397
      · exact prime_ninetyFiveCO_83641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32209312691) ^ 16104656345 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209312691) ^ 6441862538 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209312691) ^ 332054770 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209312691) ^ 81131770 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209312691) ^ 385090 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_33178454173 : Nat.Prime 33178454173 := by
  apply lucas_primality 33178454173 (2 : ZMod 33178454173)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (6053, 1), (50753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (6053, 1), (50753, 1)] : List FactorBlock).map factorBlockValue).prod) = 33178454173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_6053
      · exact prime_ninetyFiveCO_50753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33178454173) ^ 16589227086 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 33178454173) ^ 11059484724 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 33178454173) ^ 5481324 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 33178454173) ^ 653724 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_33834748711 : Nat.Prime 33834748711 := by
  apply lucas_primality 33834748711 (3 : ZMod 33834748711)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (161117851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (161117851, 1)] : List FactorBlock).map factorBlockValue).prod) = 33834748711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_161117851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33834748711) ^ 16917374355 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33834748711) ^ 11278249570 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33834748711) ^ 6766949742 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33834748711) ^ 4833535530 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33834748711) ^ 210 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_37848248371 : Nat.Prime 37848248371 := by
  apply lucas_primality 37848248371 (2 : ZMod 37848248371)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1747, 1), (240719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1747, 1), (240719, 1)] : List FactorBlock).map factorBlockValue).prod) = 37848248371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_1747
      · exact prime_ninetyFiveCO_240719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37848248371) ^ 18924124185 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37848248371) ^ 12616082790 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37848248371) ^ 7569649674 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37848248371) ^ 21664710 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37848248371) ^ 157230 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_37874595271 : Nat.Prime 37874595271 := by
  apply lucas_primality 37874595271 (6 : ZMod 37874595271)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (1163, 1), (29339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (1163, 1), (29339, 1)] : List FactorBlock).map factorBlockValue).prod) = 37874595271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_37
      · exact prime_ninetyFiveCO_1163
      · exact prime_ninetyFiveCO_29339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37874595271) ^ 18937297635 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 37874595271) ^ 12624865090 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 37874595271) ^ 7574919054 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 37874595271) ^ 1023637710 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 37874595271) ^ 32566290 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 37874595271) ^ 1290930 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_46633667599 : Nat.Prime 46633667599 := by
  apply lucas_primality 46633667599 (3 : ZMod 46633667599)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (31, 1), (568523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (31, 1), (568523, 1)] : List FactorBlock).map factorBlockValue).prod) = 46633667599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_568523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46633667599) ^ 23316833799 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 46633667599) ^ 15544555866 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 46633667599) ^ 6661952514 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 46633667599) ^ 1504311858 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 46633667599) ^ 82026 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_47439148997 : Nat.Prime 47439148997 := by
  apply lucas_primality 47439148997 (2 : ZMod 47439148997)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (83, 1), (4927207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (83, 1), (4927207, 1)] : List FactorBlock).map factorBlockValue).prod) = 47439148997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_83
      · exact prime_ninetyFiveCO_4927207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47439148997) ^ 23719574498 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47439148997) ^ 1635832724 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47439148997) ^ 571556012 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47439148997) ^ 9628 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_47846059981 : Nat.Prime 47846059981 := by
  apply lucas_primality 47846059981 (2 : ZMod 47846059981)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (113, 1), (7056941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (113, 1), (7056941, 1)] : List FactorBlock).map factorBlockValue).prod) = 47846059981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_113
      · exact prime_ninetyFiveCO_7056941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47846059981) ^ 23923029990 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47846059981) ^ 15948686660 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47846059981) ^ 9569211996 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47846059981) ^ 423416460 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47846059981) ^ 6780 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_54378402311 : Nat.Prime 54378402311 := by
  apply lucas_primality 54378402311 (7 : ZMod 54378402311)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (175414201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (175414201, 1)] : List FactorBlock).map factorBlockValue).prod) = 54378402311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_175414201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 54378402311) ^ 27189201155 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 54378402311) ^ 10875680462 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 54378402311) ^ 1754142010 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 54378402311) ^ 310 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_57412567873 : Nat.Prime 57412567873 := by
  apply lucas_primality 57412567873 (10 : ZMod 57412567873)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11, 3), (74887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11, 3), (74887, 1)] : List FactorBlock).map factorBlockValue).prod) = 57412567873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_74887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 57412567873) ^ 28706283936 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 57412567873) ^ 19137522624 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 57412567873) ^ 5219324352 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 57412567873) ^ 766656 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_63037010189 : Nat.Prime 63037010189 := by
  apply lucas_primality 63037010189 (2 : ZMod 63037010189)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15759252547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15759252547, 1)] : List FactorBlock).map factorBlockValue).prod) = 63037010189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_15759252547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 63037010189) ^ 31518505094 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 63037010189) ^ 4 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_64878580189 : Nat.Prime 64878580189 := by
  apply lucas_primality 64878580189 (2 : ZMod 64878580189)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (109, 1), (1193, 1), (13859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (109, 1), (1193, 1), (13859, 1)] : List FactorBlock).map factorBlockValue).prod) = 64878580189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_109
      · exact prime_ninetyFiveCO_1193
      · exact prime_ninetyFiveCO_13859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64878580189) ^ 32439290094 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64878580189) ^ 21626193396 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64878580189) ^ 595216332 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64878580189) ^ 54382716 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64878580189) ^ 4681332 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_70521387931 : Nat.Prime 70521387931 := by
  apply lucas_primality 70521387931 (10 : ZMod 70521387931)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (73, 1), (1533407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (73, 1), (1533407, 1)] : List FactorBlock).map factorBlockValue).prod) = 70521387931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_73
      · exact prime_ninetyFiveCO_1533407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 70521387931) ^ 35260693965 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 70521387931) ^ 23507129310 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 70521387931) ^ 14104277586 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 70521387931) ^ 10074483990 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 70521387931) ^ 966046410 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 70521387931) ^ 45990 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_77741016791 : Nat.Prime 77741016791 := by
  apply lucas_primality 77741016791 (7 : ZMod 77741016791)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1567, 1), (2011, 1), (2467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1567, 1), (2011, 1), (2467, 1)] : List FactorBlock).map factorBlockValue).prod) = 77741016791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_1567
      · exact prime_ninetyFiveCO_2011
      · exact prime_ninetyFiveCO_2467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 77741016791) ^ 38870508395 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77741016791) ^ 15548203358 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77741016791) ^ 49611370 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77741016791) ^ 38657890 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77741016791) ^ 31512370 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_88484050441 : Nat.Prime 88484050441 := by
  apply lucas_primality 88484050441 (7 : ZMod 88484050441)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (73, 1), (3366973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (73, 1), (3366973, 1)] : List FactorBlock).map factorBlockValue).prod) = 88484050441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_73
      · exact prime_ninetyFiveCO_3366973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 88484050441) ^ 44242025220 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 88484050441) ^ 29494683480 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 88484050441) ^ 17696810088 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 88484050441) ^ 1212110280 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 88484050441) ^ 26280 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_93505349653 : Nat.Prime 93505349653 := by
  apply lucas_primality 93505349653 (2 : ZMod 93505349653)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (54490297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (54490297, 1)] : List FactorBlock).map factorBlockValue).prod) = 93505349653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_54490297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93505349653) ^ 46752674826 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93505349653) ^ 31168449884 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93505349653) ^ 8500486332 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93505349653) ^ 7192719204 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93505349653) ^ 1716 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_114551507561 : Nat.Prime 114551507561 := by
  apply lucas_primality 114551507561 (3 : ZMod 114551507561)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (353, 1), (431, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (353, 1), (431, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) = 114551507561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_353
      · exact prime_ninetyFiveCO_431
      · exact prime_ninetyFiveCO_2689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 114551507561) ^ 57275753780 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114551507561) ^ 22910301512 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114551507561) ^ 16364501080 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114551507561) ^ 324508520 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114551507561) ^ 265780760 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114551507561) ^ 42600040 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_118944146147 : Nat.Prime 118944146147 := by
  apply lucas_primality 118944146147 (2 : ZMod 118944146147)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (937, 1), (1295321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (937, 1), (1295321, 1)] : List FactorBlock).map factorBlockValue).prod) = 118944146147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_937
      · exact prime_ninetyFiveCO_1295321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118944146147) ^ 59472073073 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 118944146147) ^ 16992020878 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 118944146147) ^ 126941458 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 118944146147) ^ 91826 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_130046080609 : Nat.Prime 130046080609 := by
  apply lucas_primality 130046080609 (17 : ZMod 130046080609)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 5), (43, 1), (388931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 5), (43, 1), (388931, 1)] : List FactorBlock).map factorBlockValue).prod) = 130046080609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_388931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 130046080609) ^ 65023040304 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 130046080609) ^ 43348693536 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 130046080609) ^ 3024327456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 130046080609) ^ 334368 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_152365887329 : Nat.Prime 152365887329 := by
  apply lucas_primality 152365887329 (3 : ZMod 152365887329)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (73, 1), (65225123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (73, 1), (65225123, 1)] : List FactorBlock).map factorBlockValue).prod) = 152365887329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_73
      · exact prime_ninetyFiveCO_65225123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 152365887329) ^ 76182943664 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 152365887329) ^ 2087203936 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 152365887329) ^ 2336 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_164088629401 : Nat.Prime 164088629401 := by
  apply lucas_primality 164088629401 (13 : ZMod 164088629401)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (29, 1), (877, 1), (10753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (29, 1), (877, 1), (10753, 1)] : List FactorBlock).map factorBlockValue).prod) = 164088629401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_877
      · exact prime_ninetyFiveCO_10753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 164088629401) ^ 82044314700 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 164088629401) ^ 54696209800 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 164088629401) ^ 32817725880 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 164088629401) ^ 5658228600 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 164088629401) ^ 187102200 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 164088629401) ^ 15259800 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_172223394649 : Nat.Prime 172223394649 := by
  apply lucas_primality 172223394649 (13 : ZMod 172223394649)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (377682883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (377682883, 1)] : List FactorBlock).map factorBlockValue).prod) = 172223394649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_377682883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 172223394649) ^ 86111697324 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 172223394649) ^ 57407798216 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 172223394649) ^ 9064389192 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 172223394649) ^ 456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_182230139683 : Nat.Prime 182230139683 := by
  apply lucas_primality 182230139683 (2 : ZMod 182230139683)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (557, 1), (18175757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (557, 1), (18175757, 1)] : List FactorBlock).map factorBlockValue).prod) = 182230139683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_557
      · exact prime_ninetyFiveCO_18175757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 182230139683) ^ 91115069841 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 182230139683) ^ 60743379894 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 182230139683) ^ 327163626 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 182230139683) ^ 10026 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_227247571627 : Nat.Prime 227247571627 := by
  apply lucas_primality 227247571627 (5 : ZMod 227247571627)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37874595271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37874595271, 1)] : List FactorBlock).map factorBlockValue).prod) = 227247571627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_37874595271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 227247571627) ^ 113623785813 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 227247571627) ^ 75749190542 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 227247571627) ^ 6 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_279017588441 : Nat.Prime 279017588441 := by
  apply lucas_primality 279017588441 (3 : ZMod 279017588441)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (1873, 1), (219071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (1873, 1), (219071, 1)] : List FactorBlock).map factorBlockValue).prod) = 279017588441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_1873
      · exact prime_ninetyFiveCO_219071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 279017588441) ^ 139508794220 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 279017588441) ^ 55803517688 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 279017588441) ^ 16412799320 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 279017588441) ^ 148968280 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 279017588441) ^ 1273640 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_290775460901 : Nat.Prime 290775460901 := by
  apply lucas_primality 290775460901 (2 : ZMod 290775460901)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (21157, 1), (137437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (21157, 1), (137437, 1)] : List FactorBlock).map factorBlockValue).prod) = 290775460901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_21157
      · exact prime_ninetyFiveCO_137437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 290775460901) ^ 145387730450 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 290775460901) ^ 58155092180 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 290775460901) ^ 13743700 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 290775460901) ^ 2115700 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_305893211957 : Nat.Prime 305893211957 := by
  apply lucas_primality 305893211957 (2 : ZMod 305893211957)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (1047579493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (1047579493, 1)] : List FactorBlock).map factorBlockValue).prod) = 305893211957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_73
      · exact prime_ninetyFiveCO_1047579493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 305893211957) ^ 152946605978 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 305893211957) ^ 4190317972 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 305893211957) ^ 292 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_335412278407 : Nat.Prime 335412278407 := by
  apply lucas_primality 335412278407 (3 : ZMod 335412278407)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (197, 1), (3503293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (197, 1), (3503293, 1)] : List FactorBlock).map factorBlockValue).prod) = 335412278407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_197
      · exact prime_ninetyFiveCO_3503293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 335412278407) ^ 167706139203 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335412278407) ^ 111804092802 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335412278407) ^ 1702600398 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335412278407) ^ 95742 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_338750986003 : Nat.Prime 338750986003 := by
  apply lucas_primality 338750986003 (2 : ZMod 338750986003)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (394814669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (394814669, 1)] : List FactorBlock).map factorBlockValue).prod) = 338750986003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_394814669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 338750986003) ^ 169375493001 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338750986003) ^ 112916995334 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338750986003) ^ 30795544182 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338750986003) ^ 26057768154 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338750986003) ^ 858 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_354928943749 : Nat.Prime 354928943749 := by
  apply lucas_primality 354928943749 (2 : ZMod 354928943749)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19543, 1), (1513453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19543, 1), (1513453, 1)] : List FactorBlock).map factorBlockValue).prod) = 354928943749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_19543
      · exact prime_ninetyFiveCO_1513453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 354928943749) ^ 177464471874 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 354928943749) ^ 118309647916 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 354928943749) ^ 18161436 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 354928943749) ^ 234516 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_441533777957 : Nat.Prime 441533777957 := by
  apply lucas_primality 441533777957 (2 : ZMod 441533777957)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (1397258791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (1397258791, 1)] : List FactorBlock).map factorBlockValue).prod) = 441533777957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_79
      · exact prime_ninetyFiveCO_1397258791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 441533777957) ^ 220766888978 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 441533777957) ^ 5589035164 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 441533777957) ^ 316 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_452316019283 : Nat.Prime 452316019283 := by
  apply lucas_primality 452316019283 (2 : ZMod 452316019283)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (626476481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (626476481, 1)] : List FactorBlock).map factorBlockValue).prod) = 452316019283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_626476481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 452316019283) ^ 226158009641 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 452316019283) ^ 23806106278 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 452316019283) ^ 722 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_463791639287 : Nat.Prime 463791639287 := by
  apply lucas_primality 463791639287 (5 : ZMod 463791639287)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (10082426941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (10082426941, 1)] : List FactorBlock).map factorBlockValue).prod) = 463791639287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_10082426941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 463791639287) ^ 231895819643 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 463791639287) ^ 20164853882 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 463791639287) ^ 46 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_473250259627 : Nat.Prime 473250259627 := by
  apply lucas_primality 473250259627 (3 : ZMod 473250259627)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1063, 1), (6277, 1), (11821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1063, 1), (6277, 1), (11821, 1)] : List FactorBlock).map factorBlockValue).prod) = 473250259627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_1063
      · exact prime_ninetyFiveCO_6277
      · exact prime_ninetyFiveCO_11821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 473250259627) ^ 236625129813 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 473250259627) ^ 157750086542 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 473250259627) ^ 445202502 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 473250259627) ^ 75394338 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 473250259627) ^ 40034706 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_520930663199 : Nat.Prime 520930663199 := by
  apply lucas_primality 520930663199 (7 : ZMod 520930663199)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (1277, 1), (431219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (1277, 1), (431219, 1)] : List FactorBlock).map factorBlockValue).prod) = 520930663199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_1277
      · exact prime_ninetyFiveCO_431219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 520930663199) ^ 260465331599 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 520930663199) ^ 47357333018 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 520930663199) ^ 12114666586 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 520930663199) ^ 407933174 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 520930663199) ^ 1208042 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_603333927499 : Nat.Prime 603333927499 := by
  apply lucas_primality 603333927499 (3 : ZMod 603333927499)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (383, 1), (8469271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (383, 1), (8469271, 1)] : List FactorBlock).map factorBlockValue).prod) = 603333927499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_383
      · exact prime_ninetyFiveCO_8469271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 603333927499) ^ 301666963749 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 603333927499) ^ 201111309166 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 603333927499) ^ 19462384758 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 603333927499) ^ 1575284406 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 603333927499) ^ 71238 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_610549953677 : Nat.Prime 610549953677 := by
  apply lucas_primality 610549953677 (2 : ZMod 610549953677)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (31, 1), (43, 1), (8808211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (31, 1), (43, 1), (8808211, 1)] : List FactorBlock).map factorBlockValue).prod) = 610549953677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_8808211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 610549953677) ^ 305274976838 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 610549953677) ^ 46965381052 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 610549953677) ^ 19695159796 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 610549953677) ^ 14198836132 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 610549953677) ^ 69316 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_654878088301 : Nat.Prime 654878088301 := by
  apply lucas_primality 654878088301 (2 : ZMod 654878088301)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (41, 1), (53242121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (41, 1), (53242121, 1)] : List FactorBlock).map factorBlockValue).prod) = 654878088301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_53242121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 654878088301) ^ 327439044150 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 654878088301) ^ 218292696100 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 654878088301) ^ 130975617660 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 654878088301) ^ 15972636300 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 654878088301) ^ 12300 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_690553711699 : Nat.Prime 690553711699 := by
  apply lucas_primality 690553711699 (3 : ZMod 690553711699)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (144941, 1), (794063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (144941, 1), (794063, 1)] : List FactorBlock).map factorBlockValue).prod) = 690553711699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_144941
      · exact prime_ninetyFiveCO_794063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 690553711699) ^ 345276855849 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 690553711699) ^ 230184570566 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 690553711699) ^ 4764378 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 690553711699) ^ 869646 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_813425308093 : Nat.Prime 813425308093 := by
  apply lucas_primality 813425308093 (2 : ZMod 813425308093)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (22595147447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (22595147447, 1)] : List FactorBlock).map factorBlockValue).prod) = 813425308093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_22595147447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 813425308093) ^ 406712654046 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 813425308093) ^ 271141769364 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 813425308093) ^ 36 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_944055288377 : Nat.Prime 944055288377 := by
  apply lucas_primality 944055288377 (3 : ZMod 944055288377)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (199, 1), (592999553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (199, 1), (592999553, 1)] : List FactorBlock).map factorBlockValue).prod) = 944055288377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_199
      · exact prime_ninetyFiveCO_592999553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 944055288377) ^ 472027644188 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 944055288377) ^ 4743996424 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 944055288377) ^ 1592 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1308809562707 : Nat.Prime 1308809562707 := by
  apply lucas_primality 1308809562707 (2 : ZMod 1308809562707)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2879, 1), (227302807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2879, 1), (227302807, 1)] : List FactorBlock).map factorBlockValue).prod) = 1308809562707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_2879
      · exact prime_ninetyFiveCO_227302807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1308809562707) ^ 654404781353 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308809562707) ^ 454605614 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308809562707) ^ 5758 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1553302297711 : Nat.Prime 1553302297711 := by
  apply lucas_primality 1553302297711 (6 : ZMod 1553302297711)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (3593, 1), (1601161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (3593, 1), (1601161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1553302297711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_3593
      · exact prime_ninetyFiveCO_1601161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1553302297711) ^ 776651148855 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1553302297711) ^ 517767432570 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1553302297711) ^ 310660459542 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1553302297711) ^ 432313470 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1553302297711) ^ 970110 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1996637277577 : Nat.Prime 1996637277577 := by
  apply lucas_primality 1996637277577 (5 : ZMod 1996637277577)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (4378590521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (4378590521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1996637277577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_4378590521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1996637277577) ^ 998318638788 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1996637277577) ^ 665545759192 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1996637277577) ^ 105086172504 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1996637277577) ^ 456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2151974037959 : Nat.Prime 2151974037959 := by
  apply lucas_primality 2151974037959 (7 : ZMod 2151974037959)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (132679, 1), (8109701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (132679, 1), (8109701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2151974037959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_132679
      · exact prime_ninetyFiveCO_8109701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2151974037959) ^ 1075987018979 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2151974037959) ^ 16219402 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2151974037959) ^ 265358 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2208782697007 : Nat.Prime 2208782697007 := by
  apply lucas_primality 2208782697007 (6 : ZMod 2208782697007)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (2687083573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (2687083573, 1)] : List FactorBlock).map factorBlockValue).prod) = 2208782697007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_137
      · exact prime_ninetyFiveCO_2687083573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2208782697007) ^ 1104391348503 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2208782697007) ^ 736260899002 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2208782697007) ^ 16122501438 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2208782697007) ^ 822 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2243323975141 : Nat.Prime 2243323975141 := by
  apply lucas_primality 2243323975141 (2 : ZMod 2243323975141)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (60689, 1), (205357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (60689, 1), (205357, 1)] : List FactorBlock).map factorBlockValue).prod) = 2243323975141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_60689
      · exact prime_ninetyFiveCO_205357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2243323975141) ^ 1121661987570 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2243323975141) ^ 747774658380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2243323975141) ^ 448664795028 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2243323975141) ^ 36964260 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2243323975141) ^ 10924020 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3586363891921 : Nat.Prime 3586363891921 := by
  apply lucas_primality 3586363891921 (7 : ZMod 3586363891921)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (43, 1), (115838627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (43, 1), (115838627, 1)] : List FactorBlock).map factorBlockValue).prod) = 3586363891921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_115838627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3586363891921) ^ 1793181945960 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3586363891921) ^ 1195454630640 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3586363891921) ^ 717272778384 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3586363891921) ^ 83403811440 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3586363891921) ^ 30960 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3788914682279 : Nat.Prime 3788914682279 := by
  apply lucas_primality 3788914682279 (11 : ZMod 3788914682279)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (172223394649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (172223394649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3788914682279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_172223394649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 3788914682279) ^ 1894457341139 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 3788914682279) ^ 344446789298 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 3788914682279) ^ 22 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_4098737535803 : Nat.Prime 4098737535803 := by
  apply lucas_primality 4098737535803 (5 : ZMod 4098737535803)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (163, 1), (6719, 1), (20563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (163, 1), (6719, 1), (20563, 1)] : List FactorBlock).map factorBlockValue).prod) = 4098737535803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_163
      · exact prime_ninetyFiveCO_6719
      · exact prime_ninetyFiveCO_20563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4098737535803) ^ 2049368767901 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4098737535803) ^ 585533933686 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4098737535803) ^ 315287502754 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4098737535803) ^ 25145629054 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4098737535803) ^ 610021958 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4098737535803) ^ 199325854 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_4106815988831 : Nat.Prime 4106815988831 := by
  apply lucas_primality 4106815988831 (17 : ZMod 4106815988831)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (13597, 1), (736679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (13597, 1), (736679, 1)] : List FactorBlock).map factorBlockValue).prod) = 4106815988831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_13597
      · exact prime_ninetyFiveCO_736679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 4106815988831) ^ 2053407994415 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4106815988831) ^ 821363197766 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4106815988831) ^ 100166243630 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4106815988831) ^ 302038390 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4106815988831) ^ 5574770 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_5049390257993 : Nat.Prime 5049390257993 := by
  apply lucas_primality 5049390257993 (3 : ZMod 5049390257993)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (233, 1), (93410357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (233, 1), (93410357, 1)] : List FactorBlock).map factorBlockValue).prod) = 5049390257993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_233
      · exact prime_ninetyFiveCO_93410357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5049390257993) ^ 2524695128996 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5049390257993) ^ 174116905448 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5049390257993) ^ 21671202824 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5049390257993) ^ 54056 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_5186334597373 : Nat.Prime 5186334597373 := by
  apply lucas_primality 5186334597373 (2 : ZMod 5186334597373)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5351, 1), (26922977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5351, 1), (26922977, 1)] : List FactorBlock).map factorBlockValue).prod) = 5186334597373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5351
      · exact prime_ninetyFiveCO_26922977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5186334597373) ^ 2593167298686 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5186334597373) ^ 1728778199124 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5186334597373) ^ 969227172 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5186334597373) ^ 192636 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_5220326621857 : Nat.Prime 5220326621857 := by
  apply lucas_primality 5220326621857 (5 : ZMod 5220326621857)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (54378402311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (54378402311, 1)] : List FactorBlock).map factorBlockValue).prod) = 5220326621857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_54378402311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5220326621857) ^ 2610163310928 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5220326621857) ^ 1740108873952 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5220326621857) ^ 96 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_5596040111881 : Nat.Prime 5596040111881 := by
  apply lucas_primality 5596040111881 (11 : ZMod 5596040111881)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (46633667599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (46633667599, 1)] : List FactorBlock).map factorBlockValue).prod) = 5596040111881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_46633667599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5596040111881) ^ 2798020055940 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5596040111881) ^ 1865346703960 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5596040111881) ^ 1119208022376 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5596040111881) ^ 120 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_6471425586121 : Nat.Prime 6471425586121 := by
  apply lucas_primality 6471425586121 (7 : ZMod 6471425586121)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (181, 1), (607, 1), (44623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (181, 1), (607, 1), (44623, 1)] : List FactorBlock).map factorBlockValue).prod) = 6471425586121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_181
      · exact prime_ninetyFiveCO_607
      · exact prime_ninetyFiveCO_44623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6471425586121) ^ 3235712793060 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6471425586121) ^ 2157141862040 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6471425586121) ^ 1294285117224 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6471425586121) ^ 588311416920 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6471425586121) ^ 35753732520 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6471425586121) ^ 10661327160 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6471425586121) ^ 145024440 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_7832040574541 : Nat.Prime 7832040574541 := by
  apply lucas_primality 7832040574541 (10 : ZMod 7832040574541)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (113, 2), (337013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (113, 2), (337013, 1)] : List FactorBlock).map factorBlockValue).prod) = 7832040574541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_113
      · exact prime_ninetyFiveCO_337013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7832040574541) ^ 3916020287270 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7832040574541) ^ 1566408114908 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7832040574541) ^ 1118862939220 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7832040574541) ^ 602464659580 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7832040574541) ^ 69310093580 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7832040574541) ^ 23239580 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_8034894244177 : Nat.Prime 8034894244177 := by
  apply lucas_primality 8034894244177 (5 : ZMod 8034894244177)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (53, 1), (3158370379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (53, 1), (3158370379, 1)] : List FactorBlock).map factorBlockValue).prod) = 8034894244177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_53
      · exact prime_ninetyFiveCO_3158370379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8034894244177) ^ 4017447122088 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8034894244177) ^ 2678298081392 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8034894244177) ^ 151601778192 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8034894244177) ^ 2544 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_10470476501657 : Nat.Prime 10470476501657 := by
  apply lucas_primality 10470476501657 (3 : ZMod 10470476501657)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1308809562707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1308809562707, 1)] : List FactorBlock).map factorBlockValue).prod) = 10470476501657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_1308809562707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 10470476501657) ^ 5235238250828 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10470476501657) ^ 8 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_12218173718351 : Nat.Prime 12218173718351 := by
  apply lucas_primality 12218173718351 (19 : ZMod 12218173718351)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (12861235493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (12861235493, 1)] : List FactorBlock).map factorBlockValue).prod) = 12218173718351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_12861235493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 12218173718351) ^ 6109086859175 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (19 : ZMod 12218173718351) ^ 2443634743670 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (19 : ZMod 12218173718351) ^ 643061774650 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (19 : ZMod 12218173718351) ^ 950 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_12777758420423 : Nat.Prime 12777758420423 := by
  apply lucas_primality 12777758420423 (5 : ZMod 12777758420423)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (28649682557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (28649682557, 1)] : List FactorBlock).map factorBlockValue).prod) = 12777758420423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_223
      · exact prime_ninetyFiveCO_28649682557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12777758420423) ^ 6388879210211 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12777758420423) ^ 57299365114 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12777758420423) ^ 446 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_14381973219409 : Nat.Prime 14381973219409 := by
  apply lucas_primality 14381973219409 (7 : ZMod 14381973219409)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (83, 1), (22409, 1), (161093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (83, 1), (22409, 1), (161093, 1)] : List FactorBlock).map factorBlockValue).prod) = 14381973219409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_83
      · exact prime_ninetyFiveCO_22409
      · exact prime_ninetyFiveCO_161093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14381973219409) ^ 7190986609704 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381973219409) ^ 4793991073136 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381973219409) ^ 173276785776 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381973219409) ^ 641794512 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381973219409) ^ 89277456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_15294796504517 : Nat.Prime 15294796504517 := by
  apply lucas_primality 15294796504517 (2 : ZMod 15294796504517)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1770127, 1), (2160127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1770127, 1), (2160127, 1)] : List FactorBlock).map factorBlockValue).prod) = 15294796504517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_1770127
      · exact prime_ninetyFiveCO_2160127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15294796504517) ^ 7647398252258 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15294796504517) ^ 8640508 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 15294796504517) ^ 7080508 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_18029573386037 : Nat.Prime 18029573386037 := by
  apply lucas_primality 18029573386037 (2 : ZMod 18029573386037)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1069, 1), (4216457761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1069, 1), (4216457761, 1)] : List FactorBlock).map factorBlockValue).prod) = 18029573386037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_1069
      · exact prime_ninetyFiveCO_4216457761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18029573386037) ^ 9014786693018 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18029573386037) ^ 16865831044 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18029573386037) ^ 4276 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_18472856243827 : Nat.Prime 18472856243827 := by
  apply lucas_primality 18472856243827 (2 : ZMod 18472856243827)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1283, 1), (8929, 1), (15809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1283, 1), (8929, 1), (15809, 1)] : List FactorBlock).map factorBlockValue).prod) = 18472856243827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_1283
      · exact prime_ninetyFiveCO_8929
      · exact prime_ninetyFiveCO_15809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18472856243827) ^ 9236428121913 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18472856243827) ^ 6157618747942 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18472856243827) ^ 1086638602578 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18472856243827) ^ 14398173222 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18472856243827) ^ 2068860594 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18472856243827) ^ 1168502514 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_19573333426019 : Nat.Prime 19573333426019 := by
  apply lucas_primality 19573333426019 (2 : ZMod 19573333426019)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1153, 1), (9551, 1), (24019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1153, 1), (9551, 1), (24019, 1)] : List FactorBlock).map factorBlockValue).prod) = 19573333426019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_37
      · exact prime_ninetyFiveCO_1153
      · exact prime_ninetyFiveCO_9551
      · exact prime_ninetyFiveCO_24019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19573333426019) ^ 9786666713009 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19573333426019) ^ 529009011514 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19573333426019) ^ 16976004706 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19573333426019) ^ 2049349118 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19573333426019) ^ 814910422 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_20758187622967 : Nat.Prime 20758187622967 := by
  apply lucas_primality 20758187622967 (5 : ZMod 20758187622967)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (93505349653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (93505349653, 1)] : List FactorBlock).map factorBlockValue).prod) = 20758187622967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_37
      · exact prime_ninetyFiveCO_93505349653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20758187622967) ^ 10379093811483 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 20758187622967) ^ 6919395874322 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 20758187622967) ^ 561032097918 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 20758187622967) ^ 222 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_21846968960363 : Nat.Prime 21846968960363 := by
  apply lucas_primality 21846968960363 (2 : ZMod 21846968960363)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (19, 1), (15797, 1), (399937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (19, 1), (15797, 1), (399937, 1)] : List FactorBlock).map factorBlockValue).prod) = 21846968960363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_15797
      · exact prime_ninetyFiveCO_399937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21846968960363) ^ 10923484480181 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21846968960363) ^ 3120995565766 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21846968960363) ^ 1680536073874 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21846968960363) ^ 1149840471598 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21846968960363) ^ 1382982146 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21846968960363) ^ 54626026 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_25303418826017 : Nat.Prime 25303418826017 := by
  apply lucas_primality 25303418826017 (3 : ZMod 25303418826017)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (141101, 1), (5604013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (141101, 1), (5604013, 1)] : List FactorBlock).map factorBlockValue).prod) = 25303418826017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_141101
      · exact prime_ninetyFiveCO_5604013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25303418826017) ^ 12651709413008 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25303418826017) ^ 179328416 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25303418826017) ^ 4515232 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_27605373395987 : Nat.Prime 27605373395987 := by
  apply lucas_primality 27605373395987 (2 : ZMod 27605373395987)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (229519, 1), (1466767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (229519, 1), (1466767, 1)] : List FactorBlock).map factorBlockValue).prod) = 27605373395987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_229519
      · exact prime_ninetyFiveCO_1466767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27605373395987) ^ 13802686697993 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27605373395987) ^ 673301790146 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27605373395987) ^ 120274894 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27605373395987) ^ 18820558 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_36826606530569 : Nat.Prime 36826606530569 := by
  apply lucas_primality 36826606530569 (3 : ZMod 36826606530569)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1641589, 1), (2804189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1641589, 1), (2804189, 1)] : List FactorBlock).map factorBlockValue).prod) = 36826606530569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_1641589
      · exact prime_ninetyFiveCO_2804189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36826606530569) ^ 18413303265284 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 36826606530569) ^ 22433512 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 36826606530569) ^ 13132712 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_38823658062437 : Nat.Prime 38823658062437 := by
  apply lucas_primality 38823658062437 (2 : ZMod 38823658062437)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (283, 1), (9767, 1), (15889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (283, 1), (9767, 1), (15889, 1)] : List FactorBlock).map factorBlockValue).prod) = 38823658062437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_283
      · exact prime_ninetyFiveCO_9767
      · exact prime_ninetyFiveCO_15889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38823658062437) ^ 19411829031218 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38823658062437) ^ 2986435235572 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38823658062437) ^ 2283744591908 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38823658062437) ^ 137186070892 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38823658062437) ^ 3974982908 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38823658062437) ^ 2443429924 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_42651819450761 : Nat.Prime 42651819450761 := by
  apply lucas_primality 42651819450761 (6 : ZMod 42651819450761)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (457, 2), (392737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (457, 2), (392737, 1)] : List FactorBlock).map factorBlockValue).prod) = 42651819450761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_457
      · exact prime_ninetyFiveCO_392737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 42651819450761) ^ 21325909725380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42651819450761) ^ 8530363890152 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42651819450761) ^ 3280909188520 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42651819450761) ^ 93330020680 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42651819450761) ^ 108601480 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_51863345973731 : Nat.Prime 51863345973731 := by
  apply lucas_primality 51863345973731 (2 : ZMod 51863345973731)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5186334597373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5186334597373, 1)] : List FactorBlock).map factorBlockValue).prod) = 51863345973731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_5186334597373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51863345973731) ^ 25931672986865 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51863345973731) ^ 10372669194746 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51863345973731) ^ 10 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_52070405925869 : Nat.Prime 52070405925869 := by
  apply lucas_primality 52070405925869 (2 : ZMod 52070405925869)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (10037, 1), (117905581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (10037, 1), (117905581, 1)] : List FactorBlock).map factorBlockValue).prod) = 52070405925869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_10037
      · exact prime_ninetyFiveCO_117905581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52070405925869) ^ 26035202962934 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 52070405925869) ^ 4733673265988 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 52070405925869) ^ 5187845564 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 52070405925869) ^ 441628 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_54539417190481 : Nat.Prime 54539417190481 := by
  apply lucas_primality 54539417190481 (28 : ZMod 54539417190481)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (227247571627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (227247571627, 1)] : List FactorBlock).map factorBlockValue).prod) = 54539417190481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_227247571627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (28 : ZMod 54539417190481) ^ 27269708595240 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (28 : ZMod 54539417190481) ^ 18179805730160 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (28 : ZMod 54539417190481) ^ 10907883438096 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (28 : ZMod 54539417190481) ^ 240 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_61114495635497 : Nat.Prime 61114495635497 := by
  apply lucas_primality 61114495635497 (3 : ZMod 61114495635497)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (29, 1), (173, 1), (66203707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (29, 1), (173, 1), (66203707, 1)] : List FactorBlock).map factorBlockValue).prod) = 61114495635497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_173
      · exact prime_ninetyFiveCO_66203707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61114495635497) ^ 30557247817748 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61114495635497) ^ 2657151984152 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61114495635497) ^ 2107396401224 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61114495635497) ^ 353262980552 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61114495635497) ^ 923128 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_93703551406147 : Nat.Prime 93703551406147 := by
  apply lucas_primality 93703551406147 (2 : ZMod 93703551406147)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (473250259627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (473250259627, 1)] : List FactorBlock).map factorBlockValue).prod) = 93703551406147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_473250259627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93703551406147) ^ 46851775703073 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93703551406147) ^ 31234517135382 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93703551406147) ^ 8518504673286 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93703551406147) ^ 198 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_122358372036137 : Nat.Prime 122358372036137 := by
  apply lucas_primality 122358372036137 (3 : ZMod 122358372036137)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (15294796504517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (15294796504517, 1)] : List FactorBlock).map factorBlockValue).prod) = 122358372036137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_15294796504517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 122358372036137) ^ 61179186018068 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 122358372036137) ^ 8 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_131430257769749 : Nat.Prime 131430257769749 := by
  apply lucas_primality 131430257769749 (2 : ZMod 131430257769749)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (61, 1), (4397, 1), (564533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (61, 1), (4397, 1), (564533, 1)] : List FactorBlock).map factorBlockValue).prod) = 131430257769749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_61
      · exact prime_ninetyFiveCO_4397
      · exact prime_ninetyFiveCO_564533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131430257769749) ^ 65715128884874 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 131430257769749) ^ 18775751109964 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 131430257769749) ^ 4239685734508 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 131430257769749) ^ 2154594389668 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 131430257769749) ^ 29890893284 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 131430257769749) ^ 232812356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_167756648152789 : Nat.Prime 167756648152789 := by
  apply lucas_primality 167756648152789 (6 : ZMod 167756648152789)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1553302297711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1553302297711, 1)] : List FactorBlock).map factorBlockValue).prod) = 167756648152789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_1553302297711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 167756648152789) ^ 83878324076394 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 167756648152789) ^ 55918882717596 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 167756648152789) ^ 108 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_182998620855997 : Nat.Prime 182998620855997 := by
  apply lucas_primality 182998620855997 (14 : ZMod 182998620855997)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (43, 1), (1933, 1), (16679137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (43, 1), (1933, 1), (16679137, 1)] : List FactorBlock).map factorBlockValue).prod) = 182998620855997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_1933
      · exact prime_ninetyFiveCO_16679137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 182998620855997) ^ 91499310427998 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 182998620855997) ^ 60999540285332 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 182998620855997) ^ 16636238259636 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 182998620855997) ^ 4255781880372 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 182998620855997) ^ 94670781612 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 182998620855997) ^ 10971708 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_206303665293767 : Nat.Prime 206303665293767 := by
  apply lucas_primality 206303665293767 (5 : ZMod 206303665293767)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11483, 1), (89657, 1), (100193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11483, 1), (89657, 1), (100193, 1)] : List FactorBlock).map factorBlockValue).prod) = 206303665293767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11483
      · exact prime_ninetyFiveCO_89657
      · exact prime_ninetyFiveCO_100193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 206303665293767) ^ 103151832646883 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 206303665293767) ^ 17966007602 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 206303665293767) ^ 2301032438 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 206303665293767) ^ 2059062662 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_211066316250331 : Nat.Prime 211066316250331 := by
  apply lucas_primality 211066316250331 (2 : ZMod 211066316250331)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (305893211957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (305893211957, 1)] : List FactorBlock).map factorBlockValue).prod) = 211066316250331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_305893211957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211066316250331) ^ 105533158125165 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211066316250331) ^ 70355438750110 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211066316250331) ^ 42213263250066 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211066316250331) ^ 9176796358710 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211066316250331) ^ 690 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_259483781416633 : Nat.Prime 259483781416633 := by
  apply lucas_primality 259483781416633 (5 : ZMod 259483781416633)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19889, 1), (543608237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19889, 1), (543608237, 1)] : List FactorBlock).map factorBlockValue).prod) = 259483781416633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_19889
      · exact prime_ninetyFiveCO_543608237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 259483781416633) ^ 129741890708316 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 259483781416633) ^ 86494593805544 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 259483781416633) ^ 13046597688 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 259483781416633) ^ 477336 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_391466668520381 : Nat.Prime 391466668520381 := by
  apply lucas_primality 391466668520381 (2 : ZMod 391466668520381)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19573333426019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19573333426019, 1)] : List FactorBlock).map factorBlockValue).prod) = 391466668520381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_19573333426019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 391466668520381) ^ 195733334260190 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 391466668520381) ^ 78293333704076 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 391466668520381) ^ 20 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_421614151954741 : Nat.Prime 421614151954741 := by
  apply lucas_primality 421614151954741 (2 : ZMod 421614151954741)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (1219639, 1), (1920487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (1219639, 1), (1920487, 1)] : List FactorBlock).map factorBlockValue).prod) = 421614151954741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_1219639
      · exact prime_ninetyFiveCO_1920487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421614151954741) ^ 210807075977370 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 421614151954741) ^ 140538050651580 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 421614151954741) ^ 84322830390948 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 421614151954741) ^ 345687660 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 421614151954741) ^ 219535020 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_455461538868307 : Nat.Prime 455461538868307 := by
  apply lucas_primality 455461538868307 (2 : ZMod 455461538868307)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (25303418826017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (25303418826017, 1)] : List FactorBlock).map factorBlockValue).prod) = 455461538868307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_25303418826017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 455461538868307) ^ 227730769434153 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 455461538868307) ^ 151820512956102 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 455461538868307) ^ 18 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_515572491427967 : Nat.Prime 515572491427967 := by
  apply lucas_primality 515572491427967 (5 : ZMod 515572491427967)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (36826606530569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (36826606530569, 1)] : List FactorBlock).map factorBlockValue).prod) = 515572491427967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_36826606530569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 515572491427967) ^ 257786245713983 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 515572491427967) ^ 73653213061138 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 515572491427967) ^ 14 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_534278752487681 : Nat.Prime 534278752487681 := by
  apply lucas_primality 534278752487681 (6 : ZMod 534278752487681)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (17, 1), (24553251493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (17, 1), (24553251493, 1)] : List FactorBlock).map factorBlockValue).prod) = 534278752487681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_24553251493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 534278752487681) ^ 267139376243840 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 534278752487681) ^ 106855750497536 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 534278752487681) ^ 31428161911040 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 534278752487681) ^ 21760 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_743530820875537 : Nat.Prime 743530820875537 := by
  apply lucas_primality 743530820875537 (11 : ZMod 743530820875537)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (12739, 1), (1215968713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (12739, 1), (1215968713, 1)] : List FactorBlock).map factorBlockValue).prod) = 743530820875537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_12739
      · exact prime_ninetyFiveCO_1215968713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 743530820875537) ^ 371765410437768 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 743530820875537) ^ 247843606958512 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 743530820875537) ^ 58366498224 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 743530820875537) ^ 611472 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1024321210881061 : Nat.Prime 1024321210881061 := by
  apply lucas_primality 1024321210881061 (30 : ZMod 1024321210881061)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (409, 1), (65563, 1), (636653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (409, 1), (65563, 1), (636653, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024321210881061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_409
      · exact prime_ninetyFiveCO_65563
      · exact prime_ninetyFiveCO_636653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (30 : ZMod 1024321210881061) ^ 512160605440530 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (30 : ZMod 1024321210881061) ^ 341440403627020 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (30 : ZMod 1024321210881061) ^ 204864242176212 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (30 : ZMod 1024321210881061) ^ 2504452838340 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (30 : ZMod 1024321210881061) ^ 15623464620 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (30 : ZMod 1024321210881061) ^ 1608916020 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1553412766166879 : Nat.Prime 1553412766166879 := by
  apply lucas_primality 1553412766166879 (7 : ZMod 1553412766166879)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (103, 1), (41953, 1), (9460259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (103, 1), (41953, 1), (9460259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1553412766166879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_103
      · exact prime_ninetyFiveCO_41953
      · exact prime_ninetyFiveCO_9460259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1553412766166879) ^ 776706383083439 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1553412766166879) ^ 81758566640362 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1553412766166879) ^ 15081677341426 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1553412766166879) ^ 37027453726 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1553412766166879) ^ 164204042 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2091430512780293 : Nat.Prime 2091430512780293 := by
  apply lucas_primality 2091430512780293 (2 : ZMod 2091430512780293)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (18029573386037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (18029573386037, 1)] : List FactorBlock).map factorBlockValue).prod) = 2091430512780293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_18029573386037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2091430512780293) ^ 1045715256390146 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2091430512780293) ^ 72118293544148 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2091430512780293) ^ 116 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2458531558493669 : Nat.Prime 2458531558493669 := by
  apply lucas_primality 2458531558493669 (2 : ZMod 2458531558493669)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (31, 1), (797, 1), (209049349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (31, 1), (797, 1), (209049349, 1)] : List FactorBlock).map factorBlockValue).prod) = 2458531558493669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_797
      · exact prime_ninetyFiveCO_209049349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2458531558493669) ^ 1229265779246834 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458531558493669) ^ 351218794070524 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458531558493669) ^ 144619503440804 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458531558493669) ^ 79307469628828 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458531558493669) ^ 3084732193844 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458531558493669) ^ 11760532 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_6048415751944997 : Nat.Prime 6048415751944997 := by
  apply lucas_primality 6048415751944997 (2 : ZMod 6048415751944997)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (743, 1), (88484050441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (743, 1), (88484050441, 1)] : List FactorBlock).map factorBlockValue).prod) = 6048415751944997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_743
      · exact prime_ninetyFiveCO_88484050441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6048415751944997) ^ 3024207875972498 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048415751944997) ^ 262974597910652 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048415751944997) ^ 8140532640572 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048415751944997) ^ 68356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_7587227733984193 : Nat.Prime 7587227733984193 := by
  apply lucas_primality 7587227733984193 (10 : ZMod 7587227733984193)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 2), (17, 1), (47439148997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 2), (17, 1), (47439148997, 1)] : List FactorBlock).map factorBlockValue).prod) = 7587227733984193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_47439148997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7587227733984193) ^ 3793613866992096 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7587227733984193) ^ 2529075911328064 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7587227733984193) ^ 1083889676283456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7587227733984193) ^ 446307513763776 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7587227733984193) ^ 159936 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_12235124266765811 : Nat.Prime 12235124266765811 := by
  apply lucas_primality 12235124266765811 (6 : ZMod 12235124266765811)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (109, 1), (9199, 1), (17186321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (109, 1), (9199, 1), (17186321, 1)] : List FactorBlock).map factorBlockValue).prod) = 12235124266765811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_71
      · exact prime_ninetyFiveCO_109
      · exact prime_ninetyFiveCO_9199
      · exact prime_ninetyFiveCO_17186321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12235124266765811) ^ 6117562133382905 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 12235124266765811) ^ 2447024853353162 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 12235124266765811) ^ 172325693898110 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 12235124266765811) ^ 112248846484090 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 12235124266765811) ^ 1330049382190 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 12235124266765811) ^ 711910610 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_13743574954102699 : Nat.Prime 13743574954102699 := by
  apply lucas_primality 13743574954102699 (2 : ZMod 13743574954102699)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (38823658062437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (38823658062437, 1)] : List FactorBlock).map factorBlockValue).prod) = 13743574954102699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_59
      · exact prime_ninetyFiveCO_38823658062437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13743574954102699) ^ 6871787477051349 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13743574954102699) ^ 4581191651367566 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13743574954102699) ^ 232941948374622 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13743574954102699) ^ 354 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_15467174742839011 : Nat.Prime 15467174742839011 := by
  apply lucas_primality 15467174742839011 (14 : ZMod 15467174742839011)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (515572491427967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (515572491427967, 1)] : List FactorBlock).map factorBlockValue).prod) = 15467174742839011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_515572491427967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 15467174742839011) ^ 7733587371419505 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 15467174742839011) ^ 5155724914279670 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 15467174742839011) ^ 3093434948567802 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 15467174742839011) ^ 30 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_15694831186716281 : Nat.Prime 15694831186716281 := by
  apply lucas_primality 15694831186716281 (3 : ZMod 15694831186716281)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (563, 1), (1451, 1), (5417, 1), (88667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (563, 1), (1451, 1), (5417, 1), (88667, 1)] : List FactorBlock).map factorBlockValue).prod) = 15694831186716281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_563
      · exact prime_ninetyFiveCO_1451
      · exact prime_ninetyFiveCO_5417
      · exact prime_ninetyFiveCO_88667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15694831186716281) ^ 7847415593358140 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15694831186716281) ^ 3138966237343256 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15694831186716281) ^ 27877142427560 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15694831186716281) ^ 10816561810280 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15694831186716281) ^ 2897328998840 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 15694831186716281) ^ 177008708840 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_16590710393367311 : Nat.Prime 16590710393367311 := by
  apply lucas_primality 16590710393367311 (11 : ZMod 16590710393367311)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21341, 1), (77741016791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21341, 1), (77741016791, 1)] : List FactorBlock).map factorBlockValue).prod) = 16590710393367311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_21341
      · exact prime_ninetyFiveCO_77741016791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 16590710393367311) ^ 8295355196683655 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 16590710393367311) ^ 3318142078673462 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 16590710393367311) ^ 777410167910 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 16590710393367311) ^ 213410 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_23003373942793757 : Nat.Prime 23003373942793757 := by
  apply lucas_primality 23003373942793757 (2 : ZMod 23003373942793757)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (122358372036137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (122358372036137, 1)] : List FactorBlock).map factorBlockValue).prod) = 23003373942793757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_47
      · exact prime_ninetyFiveCO_122358372036137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23003373942793757) ^ 11501686971396878 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23003373942793757) ^ 489433488144548 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23003373942793757) ^ 188 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_23909176759043557 : Nat.Prime 23909176759043557 := by
  apply lucas_primality 23909176759043557 (2 : ZMod 23909176759043557)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (103, 1), (227, 1), (28405277741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (103, 1), (227, 1), (28405277741, 1)] : List FactorBlock).map factorBlockValue).prod) = 23909176759043557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_103
      · exact prime_ninetyFiveCO_227
      · exact prime_ninetyFiveCO_28405277741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23909176759043557) ^ 11954588379521778 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23909176759043557) ^ 7969725586347852 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23909176759043557) ^ 232127929699452 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23909176759043557) ^ 105326769863628 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23909176759043557) ^ 841716 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_27402426481002761 : Nat.Prime 27402426481002761 := by
  apply lucas_primality 27402426481002761 (3 : ZMod 27402426481002761)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (23, 2), (134153, 1), (877567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (23, 2), (134153, 1), (877567, 1)] : List FactorBlock).map factorBlockValue).prod) = 27402426481002761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_134153
      · exact prime_ninetyFiveCO_877567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27402426481002761) ^ 13701213240501380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 27402426481002761) ^ 5480485296200552 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 27402426481002761) ^ 2491129680091160 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 27402426481002761) ^ 1191409847000120 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 27402426481002761) ^ 204262494920 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 27402426481002761) ^ 31225452280 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_40495866990652081 : Nat.Prime 40495866990652081 := by
  apply lucas_primality 40495866990652081 (39 : ZMod 40495866990652081)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (8034894244177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (8034894244177, 1)] : List FactorBlock).map factorBlockValue).prod) = 40495866990652081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_8034894244177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 40495866990652081) ^ 20247933495326040 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (39 : ZMod 40495866990652081) ^ 13498622330217360 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (39 : ZMod 40495866990652081) ^ 8099173398130416 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (39 : ZMod 40495866990652081) ^ 5785123855807440 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (39 : ZMod 40495866990652081) ^ 5040 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_43935174666596921 : Nat.Prime 43935174666596921 := by
  apply lucas_primality 43935174666596921 (3 : ZMod 43935174666596921)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (257, 1), (610549953677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (257, 1), (610549953677, 1)] : List FactorBlock).map factorBlockValue).prod) = 43935174666596921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_257
      · exact prime_ninetyFiveCO_610549953677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43935174666596921) ^ 21967587333298460 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 43935174666596921) ^ 8787034933319384 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 43935174666596921) ^ 6276453523799560 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 43935174666596921) ^ 170953987029560 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 43935174666596921) ^ 71960 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_44544467063701529 : Nat.Prime 44544467063701529 := by
  apply lucas_primality 44544467063701529 (3 : ZMod 44544467063701529)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (11, 1), (393797, 1), (26232677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (11, 1), (393797, 1), (26232677, 1)] : List FactorBlock).map factorBlockValue).prod) = 44544467063701529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_393797
      · exact prime_ninetyFiveCO_26232677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44544467063701529) ^ 22272233531850764 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 44544467063701529) ^ 6363495294814504 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 44544467063701529) ^ 4049497005791048 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 44544467063701529) ^ 113115303224 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 44544467063701529) ^ 1698052664 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_50066488494025369 : Nat.Prime 50066488494025369 := by
  apply lucas_primality 50066488494025369 (13 : ZMod 50066488494025369)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1783, 1), (3907, 1), (299461597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1783, 1), (3907, 1), (299461597, 1)] : List FactorBlock).map factorBlockValue).prod) = 50066488494025369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_1783
      · exact prime_ninetyFiveCO_3907
      · exact prime_ninetyFiveCO_299461597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 50066488494025369) ^ 25033244247012684 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 50066488494025369) ^ 16688829498008456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 50066488494025369) ^ 28079915027496 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 50066488494025369) ^ 12814560658824 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 50066488494025369) ^ 167188344 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_50467353693716413 : Nat.Prime 50467353693716413 := by
  apply lucas_primality 50467353693716413 (2 : ZMod 50467353693716413)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (644143, 1), (2176334969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (644143, 1), (2176334969, 1)] : List FactorBlock).map factorBlockValue).prod) = 50467353693716413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_644143
      · exact prime_ninetyFiveCO_2176334969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50467353693716413) ^ 25233676846858206 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467353693716413) ^ 16822451231238804 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467353693716413) ^ 78348058884 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467353693716413) ^ 23189148 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_64376909959863047 : Nat.Prime 64376909959863047 := by
  apply lucas_primality 64376909959863047 (5 : ZMod 64376909959863047)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (53, 1), (61, 1), (180749, 1), (605309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (53, 1), (61, 1), (180749, 1), (605309, 1)] : List FactorBlock).map factorBlockValue).prod) = 64376909959863047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_53
      · exact prime_ninetyFiveCO_61
      · exact prime_ninetyFiveCO_180749
      · exact prime_ninetyFiveCO_605309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 64376909959863047) ^ 32188454979931523 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64376909959863047) ^ 9196701422837578 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64376909959863047) ^ 4952069996912542 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64376909959863047) ^ 1214658678487982 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64376909959863047) ^ 1055359179669886 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64376909959863047) ^ 356167447454 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64376909959863047) ^ 106353796094 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_72511893176675599 : Nat.Prime 72511893176675599 := by
  apply lucas_primality 72511893176675599 (3 : ZMod 72511893176675599)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (59, 1), (197, 1), (383, 1), (29191609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (59, 1), (197, 1), (383, 1), (29191609, 1)] : List FactorBlock).map factorBlockValue).prod) = 72511893176675599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_59
      · exact prime_ninetyFiveCO_197
      · exact prime_ninetyFiveCO_383
      · exact prime_ninetyFiveCO_29191609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72511893176675599) ^ 36255946588337799 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72511893176675599) ^ 24170631058891866 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72511893176675599) ^ 2339093328279858 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72511893176675599) ^ 1229015138587722 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72511893176675599) ^ 368080676023734 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72511893176675599) ^ 189326091845106 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72511893176675599) ^ 2483997822 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_77042245992586123 : Nat.Prime 77042245992586123 := by
  apply lucas_primality 77042245992586123 (3 : ZMod 77042245992586123)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (109, 1), (1996637277577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (109, 1), (1996637277577, 1)] : List FactorBlock).map factorBlockValue).prod) = 77042245992586123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_59
      · exact prime_ninetyFiveCO_109
      · exact prime_ninetyFiveCO_1996637277577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 77042245992586123) ^ 38521122996293061 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77042245992586123) ^ 25680748664195374 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77042245992586123) ^ 1305800779535358 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77042245992586123) ^ 706809596262258 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77042245992586123) ^ 38586 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_109787493036599671 : Nat.Prime 109787493036599671 := by
  apply lucas_primality 109787493036599671 (3 : ZMod 109787493036599671)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (157897, 1), (23177027437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (157897, 1), (23177027437, 1)] : List FactorBlock).map factorBlockValue).prod) = 109787493036599671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_157897
      · exact prime_ninetyFiveCO_23177027437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109787493036599671) ^ 54893746518299835 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 109787493036599671) ^ 36595831012199890 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 109787493036599671) ^ 21957498607319934 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 109787493036599671) ^ 695310823110 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 109787493036599671) ^ 4736910 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_134730826308802931 : Nat.Prime 134730826308802931 := by
  apply lucas_primality 134730826308802931 (2 : ZMod 134730826308802931)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (112643, 1), (149197, 1), (801683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (112643, 1), (149197, 1), (801683, 1)] : List FactorBlock).map factorBlockValue).prod) = 134730826308802931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_112643
      · exact prime_ninetyFiveCO_149197
      · exact prime_ninetyFiveCO_801683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 134730826308802931) ^ 67365413154401465 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 134730826308802931) ^ 26946165261760586 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 134730826308802931) ^ 1196086985510 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 134730826308802931) ^ 903039781690 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 134730826308802931) ^ 168059976710 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_313807297228000127 : Nat.Prime 313807297228000127 := by
  apply lucas_primality 313807297228000127 (5 : ZMod 313807297228000127)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (89833, 1), (11124935123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (89833, 1), (11124935123, 1)] : List FactorBlock).map factorBlockValue).prod) = 313807297228000127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_157
      · exact prime_ninetyFiveCO_89833
      · exact prime_ninetyFiveCO_11124935123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 313807297228000127) ^ 156903648614000063 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 313807297228000127) ^ 1998772593808918 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 313807297228000127) ^ 3493229628622 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 313807297228000127) ^ 28207562 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_426348071307079169 : Nat.Prime 426348071307079169 := by
  apply lucas_primality 426348071307079169 (3 : ZMod 426348071307079169)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (13, 1), (29, 1), (2208782697007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (13, 1), (29, 1), (2208782697007, 1)] : List FactorBlock).map factorBlockValue).prod) = 426348071307079169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_2208782697007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 426348071307079169) ^ 213174035653539584 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 426348071307079169) ^ 32796005485159936 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 426348071307079169) ^ 14701657631278592 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 426348071307079169) ^ 193024 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_689664314617844861 : Nat.Prime 689664314617844861 := by
  apply lucas_primality 689664314617844861 (2 : ZMod 689664314617844861)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (409, 1), (53887, 1), (223512803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (409, 1), (53887, 1), (223512803, 1)] : List FactorBlock).map factorBlockValue).prod) = 689664314617844861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_409
      · exact prime_ninetyFiveCO_53887
      · exact prime_ninetyFiveCO_223512803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 689664314617844861) ^ 344832157308922430 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 689664314617844861) ^ 137932862923568972 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 689664314617844861) ^ 98523473516834980 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 689664314617844861) ^ 1686220818136540 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 689664314617844861) ^ 12798343099780 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 689664314617844861) ^ 3085569620 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_780985664076995921 : Nat.Prime 780985664076995921 := by
  apply lucas_primality 780985664076995921 (3 : ZMod 780985664076995921)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (47, 1), (12218173718351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (47, 1), (12218173718351, 1)] : List FactorBlock).map factorBlockValue).prod) = 780985664076995921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_47
      · exact prime_ninetyFiveCO_12218173718351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 780985664076995921) ^ 390492832038497960 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 780985664076995921) ^ 156197132815399184 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 780985664076995921) ^ 45940333180999760 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 780985664076995921) ^ 16616716256957360 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 780985664076995921) ^ 63920 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_846297369703621133 : Nat.Prime 846297369703621133 := by
  apply lucas_primality 846297369703621133 (2 : ZMod 846297369703621133)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1607, 1), (528403, 1), (22651093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1607, 1), (528403, 1), (22651093, 1)] : List FactorBlock).map factorBlockValue).prod) = 846297369703621133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_1607
      · exact prime_ninetyFiveCO_528403
      · exact prime_ninetyFiveCO_22651093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 846297369703621133) ^ 423148684851810566 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 846297369703621133) ^ 76936124518511012 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 846297369703621133) ^ 526631841757076 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 846297369703621133) ^ 1601613483844 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 846297369703621133) ^ 37362319324 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1007192738240212631 : Nat.Prime 1007192738240212631 := by
  apply lucas_primality 1007192738240212631 (14 : ZMod 1007192738240212631)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (461, 1), (463, 1), (883, 1), (6004543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (461, 1), (463, 1), (883, 1), (6004543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007192738240212631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_89
      · exact prime_ninetyFiveCO_461
      · exact prime_ninetyFiveCO_463
      · exact prime_ninetyFiveCO_883
      · exact prime_ninetyFiveCO_6004543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1007192738240212631) ^ 503596369120106315 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1007192738240212631) ^ 201438547648042526 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1007192738240212631) ^ 11316772339777670 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1007192738240212631) ^ 2184799866030830 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1007192738240212631) ^ 2175362285616010 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1007192738240212631) ^ 1140648627678610 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 1007192738240212631) ^ 167738450410 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1099126124436642227 : Nat.Prime 1099126124436642227 := by
  apply lucas_primality 1099126124436642227 (2 : ZMod 1099126124436642227)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (41899643, 1), (771539723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (41899643, 1), (771539723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1099126124436642227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_41899643
      · exact prime_ninetyFiveCO_771539723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1099126124436642227) ^ 549563062218321113 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1099126124436642227) ^ 64654477908037778 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1099126124436642227) ^ 26232350582 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1099126124436642227) ^ 1424587862 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1781736691715230381 : Nat.Prime 1781736691715230381 := by
  apply lucas_primality 1781736691715230381 (6 : ZMod 1781736691715230381)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (13921, 1), (164088629401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (13921, 1), (164088629401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1781736691715230381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_13921
      · exact prime_ninetyFiveCO_164088629401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1781736691715230381) ^ 890868345857615190 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1781736691715230381) ^ 593912230571743460 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1781736691715230381) ^ 356347338343046076 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1781736691715230381) ^ 137056668593479260 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1781736691715230381) ^ 127989130932780 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1781736691715230381) ^ 10858380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1836994111641990079 : Nat.Prime 1836994111641990079 := by
  apply lucas_primality 1836994111641990079 (7 : ZMod 1836994111641990079)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (443, 1), (1867, 1), (8747, 1), (42320359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (443, 1), (1867, 1), (8747, 1), (42320359, 1)] : List FactorBlock).map factorBlockValue).prod) = 1836994111641990079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_443
      · exact prime_ninetyFiveCO_1867
      · exact prime_ninetyFiveCO_8747
      · exact prime_ninetyFiveCO_42320359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1836994111641990079) ^ 918497055820995039 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836994111641990079) ^ 612331370547330026 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836994111641990079) ^ 4146713570297946 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836994111641990079) ^ 983928286899834 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836994111641990079) ^ 210014189052474 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836994111641990079) ^ 43406865042 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2072037954117322787 : Nat.Prime 2072037954117322787 := by
  apply lucas_primality 2072037954117322787 (5 : ZMod 2072037954117322787)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (293, 1), (809, 1), (20141501117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (293, 1), (809, 1), (20141501117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072037954117322787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_293
      · exact prime_ninetyFiveCO_809
      · exact prime_ninetyFiveCO_20141501117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2072037954117322787) ^ 1036018977058661393 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2072037954117322787) ^ 296005422016760398 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2072037954117322787) ^ 66839934003784606 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2072037954117322787) ^ 7071801891185402 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2072037954117322787) ^ 2561233565039954 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2072037954117322787) ^ 102874058 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_5321594789619719629 : Nat.Prime 5321594789619719629 := by
  apply lucas_primality 5321594789619719629 (2 : ZMod 5321594789619719629)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (857, 1), (2309, 1), (2836799947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (857, 1), (2309, 1), (2836799947, 1)] : List FactorBlock).map factorBlockValue).prod) = 5321594789619719629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_79
      · exact prime_ninetyFiveCO_857
      · exact prime_ninetyFiveCO_2309
      · exact prime_ninetyFiveCO_2836799947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5321594789619719629) ^ 2660797394809859814 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5321594789619719629) ^ 1773864929873239876 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5321594789619719629) ^ 67361959362274932 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5321594789619719629) ^ 6209562181586604 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5321594789619719629) ^ 2304718401740892 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5321594789619719629) ^ 1875914724 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_5701691784153795713 : Nat.Prime 5701691784153795713 := by
  apply lucas_primality 5701691784153795713 (3 : ZMod 5701691784153795713)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (44544467063701529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (44544467063701529, 1)] : List FactorBlock).map factorBlockValue).prod) = 5701691784153795713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_44544467063701529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5701691784153795713) ^ 2850845892076897856 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5701691784153795713) ^ 128 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_6838024553086457303 : Nat.Prime 6838024553086457303 := by
  apply lucas_primality 6838024553086457303 (5 : ZMod 6838024553086457303)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (23909176759043557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (23909176759043557, 1)] : List FactorBlock).map factorBlockValue).prod) = 6838024553086457303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_23909176759043557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6838024553086457303) ^ 3419012276543228651 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6838024553086457303) ^ 621638595735132482 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6838024553086457303) ^ 526001888698958254 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6838024553086457303) ^ 286 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_6874028326989678859 : Nat.Prime 6874028326989678859 := by
  apply lucas_primality 6874028326989678859 (2 : ZMod 6874028326989678859)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (151, 1), (7587227733984193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (151, 1), (7587227733984193, 1)] : List FactorBlock).map factorBlockValue).prod) = 6874028326989678859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_151
      · exact prime_ninetyFiveCO_7587227733984193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6874028326989678859) ^ 3437014163494839429 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6874028326989678859) ^ 2291342775663226286 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6874028326989678859) ^ 45523366403905158 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6874028326989678859) ^ 906 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_6965555776454169217 : Nat.Prime 6965555776454169217 := by
  apply lucas_primality 6965555776454169217 (10 : ZMod 6965555776454169217)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 1), (1319, 1), (654878088301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 1), (1319, 1), (654878088301, 1)] : List FactorBlock).map factorBlockValue).prod) = 6965555776454169217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_1319
      · exact prime_ninetyFiveCO_654878088301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6965555776454169217) ^ 3482777888227084608 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 6965555776454169217) ^ 2321851925484723072 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 6965555776454169217) ^ 995079396636309888 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 6965555776454169217) ^ 5280936904059264 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 6965555776454169217) ^ 10636416 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_11586851062557052067 : Nat.Prime 11586851062557052067 := by
  apply lucas_primality 11586851062557052067 (2 : ZMod 11586851062557052067)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (134730826308802931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (134730826308802931, 1)] : List FactorBlock).map factorBlockValue).prod) = 11586851062557052067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_134730826308802931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11586851062557052067) ^ 5793425531278526033 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11586851062557052067) ^ 269461652617605862 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11586851062557052067) ^ 86 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_17342781035348459461 : Nat.Prime 17342781035348459461 := by
  apply lucas_primality 17342781035348459461 (2 : ZMod 17342781035348459461)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (37, 1), (43, 1), (154267, 1), (493369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (37, 1), (43, 1), (154267, 1), (493369, 1)] : List FactorBlock).map factorBlockValue).prod) = 17342781035348459461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_37
      · exact prime_ninetyFiveCO_43
      · exact prime_ninetyFiveCO_154267
      · exact prime_ninetyFiveCO_493369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17342781035348459461) ^ 8671390517674229730 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 5780927011782819820 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 3468556207069691892 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 2477540147906922780 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 1576616457758950860 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 559444549527369660 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 468723811766174580 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 403320489194150220 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 112420550314380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17342781035348459461) ^ 35151744506340 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_23598792139855811041 : Nat.Prime 23598792139855811041 := by
  apply lucas_primality 23598792139855811041 (13 : ZMod 23598792139855811041)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (337, 1), (3978167, 1), (12224029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (337, 1), (3978167, 1), (12224029, 1)] : List FactorBlock).map factorBlockValue).prod) = 23598792139855811041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_337
      · exact prime_ninetyFiveCO_3978167
      · exact prime_ninetyFiveCO_12224029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 23598792139855811041) ^ 11799396069927905520 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 23598792139855811041) ^ 7866264046618603680 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 23598792139855811041) ^ 4719758427971162208 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 23598792139855811041) ^ 70026089435773920 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 23598792139855811041) ^ 5932076793120 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 23598792139855811041) ^ 1930524881760 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_28083786804509413303 : Nat.Prime 28083786804509413303 := by
  apply lucas_primality 28083786804509413303 (3 : ZMod 28083786804509413303)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (641, 1), (5813, 1), (32209312691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (641, 1), (5813, 1), (32209312691, 1)] : List FactorBlock).map factorBlockValue).prod) = 28083786804509413303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_641
      · exact prime_ninetyFiveCO_5813
      · exact prime_ninetyFiveCO_32209312691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28083786804509413303) ^ 14041893402254706651 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28083786804509413303) ^ 9361262268169804434 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28083786804509413303) ^ 2160291292654570254 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28083786804509413303) ^ 43812459913431222 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28083786804509413303) ^ 4831203647773854 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28083786804509413303) ^ 871915122 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_48736968186178324181 : Nat.Prime 48736968186178324181 := by
  apply lucas_primality 48736968186178324181 (2 : ZMod 48736968186178324181)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (18541, 1), (131430257769749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (18541, 1), (131430257769749, 1)] : List FactorBlock).map factorBlockValue).prod) = 48736968186178324181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_18541
      · exact prime_ninetyFiveCO_131430257769749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48736968186178324181) ^ 24368484093089162090 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 48736968186178324181) ^ 9747393637235664836 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 48736968186178324181) ^ 2628605155394980 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 48736968186178324181) ^ 370820 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_60878615662232024639 : Nat.Prime 60878615662232024639 := by
  apply lucas_primality 60878615662232024639 (11 : ZMod 60878615662232024639)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (313807297228000127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (313807297228000127, 1)] : List FactorBlock).map factorBlockValue).prod) = 60878615662232024639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_97
      · exact prime_ninetyFiveCO_313807297228000127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 60878615662232024639) ^ 30439307831116012319 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 60878615662232024639) ^ 627614594456000254 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 60878615662232024639) ^ 194 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_188665359233372641889 : Nat.Prime 188665359233372641889 := by
  apply lucas_primality 188665359233372641889 (3 : ZMod 188665359233372641889)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (41, 1), (379, 1), (1069, 1), (354928943749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (41, 1), (379, 1), (1069, 1), (354928943749, 1)] : List FactorBlock).map factorBlockValue).prod) = 188665359233372641889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_379
      · exact prime_ninetyFiveCO_1069
      · exact prime_ninetyFiveCO_354928943749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 188665359233372641889) ^ 94332679616686320944 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 188665359233372641889) ^ 4601594127643235168 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 188665359233372641889) ^ 497797781618397472 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 188665359233372641889) ^ 176487707421302752 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 188665359233372641889) ^ 531558112 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_480703110407751835543 : Nat.Prime 480703110407751835543 := by
  apply lucas_primality 480703110407751835543 (6 : ZMod 480703110407751835543)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (743, 1), (7413023, 1), (14545930913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (743, 1), (7413023, 1), (14545930913, 1)] : List FactorBlock).map factorBlockValue).prod) = 480703110407751835543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_743
      · exact prime_ninetyFiveCO_7413023
      · exact prime_ninetyFiveCO_14545930913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 480703110407751835543) ^ 240351555203875917771 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 480703110407751835543) ^ 160234370135917278514 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 480703110407751835543) ^ 646975922486879994 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 480703110407751835543) ^ 64845760010154 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 480703110407751835543) ^ 33047256534 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_812510132307383976889 : Nat.Prime 812510132307383976889 := by
  apply lucas_primality 812510132307383976889 (13 : ZMod 812510132307383976889)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2767, 1), (12235124266765811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2767, 1), (12235124266765811, 1)] : List FactorBlock).map factorBlockValue).prod) = 812510132307383976889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_2767
      · exact prime_ninetyFiveCO_12235124266765811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 812510132307383976889) ^ 406255066153691988444 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 812510132307383976889) ^ 270836710769127992296 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 812510132307383976889) ^ 293642982402379464 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 812510132307383976889) ^ 66408 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_926745708477208575089 : Nat.Prime 926745708477208575089 := by
  apply lucas_primality 926745708477208575089 (3 : ZMod 926745708477208575089)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (241, 1), (6577, 1), (5220326621857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (241, 1), (6577, 1), (5220326621857, 1)] : List FactorBlock).map factorBlockValue).prod) = 926745708477208575089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_241
      · exact prime_ninetyFiveCO_6577
      · exact prime_ninetyFiveCO_5220326621857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 926745708477208575089) ^ 463372854238604287544 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 926745708477208575089) ^ 132392244068172653584 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 926745708477208575089) ^ 3845417877498790768 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 926745708477208575089) ^ 140907056177164144 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 926745708477208575089) ^ 177526384 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1027664778478097715031 : Nat.Prime 1027664778478097715031 := by
  apply lucas_primality 1027664778478097715031 (6 : ZMod 1027664778478097715031)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2399, 1), (2909, 1), (4457, 1), (367106741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2399, 1), (2909, 1), (4457, 1), (367106741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1027664778478097715031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_2399
      · exact prime_ninetyFiveCO_2909
      · exact prime_ninetyFiveCO_4457
      · exact prime_ninetyFiveCO_367106741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1027664778478097715031) ^ 513832389239048857515 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027664778478097715031) ^ 342554926159365905010 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027664778478097715031) ^ 205532955695619543006 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027664778478097715031) ^ 428372146093412970 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027664778478097715031) ^ 353270807314574670 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027664778478097715031) ^ 230573205851042790 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027664778478097715031) ^ 2799362320830 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_2765787662637864579139 : Nat.Prime 2765787662637864579139 := by
  apply lucas_primality 2765787662637864579139 (3 : ZMod 2765787662637864579139)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (691, 1), (23003373942793757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (691, 1), (23003373942793757, 1)] : List FactorBlock).map factorBlockValue).prod) = 2765787662637864579139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_691
      · exact prime_ninetyFiveCO_23003373942793757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2765787662637864579139) ^ 1382893831318932289569 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2765787662637864579139) ^ 921929220879288193046 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2765787662637864579139) ^ 95371988366822916522 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2765787662637864579139) ^ 4002587066046113718 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2765787662637864579139) ^ 120234 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_4303298461831613127181 : Nat.Prime 4303298461831613127181 := by
  apply lucas_primality 4303298461831613127181 (17 : ZMod 4303298461831613127181)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (131, 1), (16590710393367311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (131, 1), (16590710393367311, 1)] : List FactorBlock).map factorBlockValue).prod) = 4303298461831613127181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_131
      · exact prime_ninetyFiveCO_16590710393367311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 4303298461831613127181) ^ 2151649230915806563590 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4303298461831613127181) ^ 1434432820610537709060 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4303298461831613127181) ^ 860659692366322625436 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4303298461831613127181) ^ 391208951075601193380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4303298461831613127181) ^ 32849606578867275780 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (17 : ZMod 4303298461831613127181) ^ 259380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_4406143073045047356761 : Nat.Prime 4406143073045047356761 := by
  apply lucas_primality 4406143073045047356761 (3 : ZMod 4406143073045047356761)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (173, 1), (1847, 1), (1300709, 1), (265036361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (173, 1), (1847, 1), (1300709, 1), (265036361, 1)] : List FactorBlock).map factorBlockValue).prod) = 4406143073045047356761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_173
      · exact prime_ninetyFiveCO_1847
      · exact prime_ninetyFiveCO_1300709
      · exact prime_ninetyFiveCO_265036361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4406143073045047356761) ^ 2203071536522523678380 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4406143073045047356761) ^ 881228614609009471352 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4406143073045047356761) ^ 25469035104306632120 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4406143073045047356761) ^ 2385567446153247080 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4406143073045047356761) ^ 3387493338667640 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4406143073045047356761) ^ 16624673899160 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_5263592564107259011549 : Nat.Prime 5263592564107259011549 := by
  apply lucas_primality 5263592564107259011549 (2 : ZMod 5263592564107259011549)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (48736968186178324181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (48736968186178324181, 1)] : List FactorBlock).map factorBlockValue).prod) = 5263592564107259011549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_48736968186178324181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5263592564107259011549) ^ 2631796282053629505774 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5263592564107259011549) ^ 1754530854702419670516 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5263592564107259011549) ^ 108 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_8950486112287993278377 : Nat.Prime 8950486112287993278377 := by
  apply lucas_primality 8950486112287993278377 (3 : ZMod 8950486112287993278377)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (3167, 1), (50467353693716413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (3167, 1), (50467353693716413, 1)] : List FactorBlock).map factorBlockValue).prod) = 8950486112287993278377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_3167
      · exact prime_ninetyFiveCO_50467353693716413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8950486112287993278377) ^ 4475243056143996639188 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8950486112287993278377) ^ 1278640873183999039768 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8950486112287993278377) ^ 2826171806848119128 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8950486112287993278377) ^ 177352 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_9578842197378376797841 : Nat.Prime 9578842197378376797841 := by
  apply lucas_primality 9578842197378376797841 (13 : ZMod 9578842197378376797841)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (5701691784153795713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (5701691784153795713, 1)] : List FactorBlock).map factorBlockValue).prod) = 9578842197378376797841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_5701691784153795713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9578842197378376797841) ^ 4789421098689188398920 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 9578842197378376797841) ^ 3192947399126125599280 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 9578842197378376797841) ^ 1915768439475675359568 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 9578842197378376797841) ^ 1368406028196910971120 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 9578842197378376797841) ^ 1680 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_10960376773634766189311 : Nat.Prime 10960376773634766189311 := by
  apply lucas_primality 10960376773634766189311 (13 : ZMod 10960376773634766189311)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (40787, 1), (455461538868307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (40787, 1), (455461538868307, 1)] : List FactorBlock).map factorBlockValue).prod) = 10960376773634766189311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_59
      · exact prime_ninetyFiveCO_40787
      · exact prime_ninetyFiveCO_455461538868307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10960376773634766189311) ^ 5480188386817383094655 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 10960376773634766189311) ^ 2192075354726953237862 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 10960376773634766189311) ^ 185769097858216376090 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 10960376773634766189311) ^ 268722307932301130 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 10960376773634766189311) ^ 24064330 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_11603941865665812426131 : Nat.Prime 11603941865665812426131 := by
  apply lucas_primality 11603941865665812426131 (2 : ZMod 11603941865665812426131)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (103, 1), (4273, 1), (11162993, 1), (236186339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (103, 1), (4273, 1), (11162993, 1), (236186339, 1)] : List FactorBlock).map factorBlockValue).prod) = 11603941865665812426131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_103
      · exact prime_ninetyFiveCO_4273
      · exact prime_ninetyFiveCO_11162993
      · exact prime_ninetyFiveCO_236186339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11603941865665812426131) ^ 5801970932832906213065 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11603941865665812426131) ^ 2320788373133162485226 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11603941865665812426131) ^ 112659629763745751710 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11603941865665812426131) ^ 2715642842421205810 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11603941865665812426131) ^ 1039500953343410 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11603941865665812426131) ^ 49130453161670 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_14620077559096887717739 : Nat.Prime 14620077559096887717739 := by
  apply lucas_primality 14620077559096887717739 (7 : ZMod 14620077559096887717739)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (79, 1), (97, 1), (403703, 1), (13818559351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (79, 1), (97, 1), (403703, 1), (13818559351, 1)] : List FactorBlock).map factorBlockValue).prod) = 14620077559096887717739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_79
      · exact prime_ninetyFiveCO_97
      · exact prime_ninetyFiveCO_403703
      · exact prime_ninetyFiveCO_13818559351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14620077559096887717739) ^ 7310038779548443858869 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14620077559096887717739) ^ 4873359186365629239246 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14620077559096887717739) ^ 769477766268257248302 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14620077559096887717739) ^ 185064272899960604022 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14620077559096887717739) ^ 150722449062854512554 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14620077559096887717739) ^ 36214934144895846 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 14620077559096887717739) ^ 1058003022438 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_17688981080695948046797 : Nat.Prime 17688981080695948046797 := by
  apply lucas_primality 17688981080695948046797 (6 : ZMod 17688981080695948046797)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (277, 1), (5321594789619719629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (277, 1), (5321594789619719629, 1)] : List FactorBlock).map factorBlockValue).prod) = 17688981080695948046797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_277
      · exact prime_ninetyFiveCO_5321594789619719629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 17688981080695948046797) ^ 8844490540347974023398 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 17688981080695948046797) ^ 5896327026898649348932 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 17688981080695948046797) ^ 63859137475436635548 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 17688981080695948046797) ^ 3324 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_27280203713673317563397 : Nat.Prime 27280203713673317563397 := by
  apply lucas_primality 27280203713673317563397 (2 : ZMod 27280203713673317563397)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 2), (23598792139855811041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 2), (23598792139855811041, 1)] : List FactorBlock).map factorBlockValue).prod) = 27280203713673317563397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_23598792139855811041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27280203713673317563397) ^ 13640101856836658781698 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27280203713673317563397) ^ 1604717865510195150788 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27280203713673317563397) ^ 1156 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_79310575314810852421699 : Nat.Prime 79310575314810852421699 := by
  apply lucas_primality 79310575314810852421699 (3 : ZMod 79310575314810852421699)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4406143073045047356761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4406143073045047356761, 1)] : List FactorBlock).map factorBlockValue).prod) = 79310575314810852421699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_4406143073045047356761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 79310575314810852421699) ^ 39655287657405426210849 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 79310575314810852421699) ^ 26436858438270284140566 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 79310575314810852421699) ^ 18 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_297286287499187747586247 : Nat.Prime 297286287499187747586247 := by
  apply lucas_primality 297286287499187747586247 (3 : ZMod 297286287499187747586247)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (911, 1), (5495051, 1), (520930663199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (911, 1), (5495051, 1), (520930663199, 1)] : List FactorBlock).map factorBlockValue).prod) = 297286287499187747586247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_19
      · exact prime_ninetyFiveCO_911
      · exact prime_ninetyFiveCO_5495051
      · exact prime_ninetyFiveCO_520930663199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 297286287499187747586247) ^ 148643143749593873793123 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 297286287499187747586247) ^ 99095429166395915862082 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 297286287499187747586247) ^ 15646646710483565662434 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 297286287499187747586247) ^ 326329624038625408986 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 297286287499187747586247) ^ 54100733095868946 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 297286287499187747586247) ^ 570683026554 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_654358222286900230791877 : Nat.Prime 654358222286900230791877 := by
  apply lucas_primality 654358222286900230791877 (5 : ZMod 654358222286900230791877)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (132036193, 1), (3788914682279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (132036193, 1), (3788914682279, 1)] : List FactorBlock).map factorBlockValue).prod) = 654358222286900230791877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_109
      · exact prime_ninetyFiveCO_132036193
      · exact prime_ninetyFiveCO_3788914682279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 654358222286900230791877) ^ 327179111143450115395938 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 654358222286900230791877) ^ 218119407428966743597292 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 654358222286900230791877) ^ 6003286442999084686164 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 654358222286900230791877) ^ 4955900404420932 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 654358222286900230791877) ^ 172703340444 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_711829805238605494939787 : Nat.Prime 711829805238605494939787 := by
  apply lucas_primality 711829805238605494939787 (2 : ZMod 711829805238605494939787)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (619, 1), (4519, 1), (30509, 1), (36479, 1), (114325283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (619, 1), (4519, 1), (30509, 1), (36479, 1), (114325283, 1)] : List FactorBlock).map factorBlockValue).prod) = 711829805238605494939787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_619
      · exact prime_ninetyFiveCO_4519
      · exact prime_ninetyFiveCO_30509
      · exact prime_ninetyFiveCO_36479
      · exact prime_ninetyFiveCO_114325283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 711829805238605494939787) ^ 355914902619302747469893 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 711829805238605494939787) ^ 1149967375183530686494 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 711829805238605494939787) ^ 157519319592521685094 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 711829805238605494939787) ^ 23331797346311104754 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 711829805238605494939787) ^ 19513413340239740534 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 711829805238605494939787) ^ 6226355068271342 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_959263389757596014976977 : Nat.Prime 959263389757596014976977 := by
  apply lucas_primality 959263389757596014976977 (6 : ZMod 959263389757596014976977)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (17, 1), (353, 1), (109787493036599671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (17, 1), (353, 1), (109787493036599671, 1)] : List FactorBlock).map factorBlockValue).prod) = 959263389757596014976977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_353
      · exact prime_ninetyFiveCO_109787493036599671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 959263389757596014976977) ^ 479631694878798007488488 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 959263389757596014976977) ^ 137037627108228002139568 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 959263389757596014976977) ^ 73789491519815078075152 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 959263389757596014976977) ^ 56427258221035059704528 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 959263389757596014976977) ^ 2717460027641915056592 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (6 : ZMod 959263389757596014976977) ^ 8737456 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1783717724995126485517483 : Nat.Prime 1783717724995126485517483 := by
  apply lucas_primality 1783717724995126485517483 (2 : ZMod 1783717724995126485517483)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (297286287499187747586247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (297286287499187747586247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1783717724995126485517483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_297286287499187747586247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1783717724995126485517483) ^ 891858862497563242758741 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1783717724995126485517483) ^ 594572574998375495172494 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1783717724995126485517483) ^ 6 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3419140734566292106717993 : Nat.Prime 3419140734566292106717993 := by
  apply lucas_primality 3419140734566292106717993 (5 : ZMod 3419140734566292106717993)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (31, 1), (452533, 1), (8661061, 1), (130280729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (31, 1), (452533, 1), (8661061, 1), (130280729, 1)] : List FactorBlock).map factorBlockValue).prod) = 3419140734566292106717993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_452533
      · exact prime_ninetyFiveCO_8661061
      · exact prime_ninetyFiveCO_130280729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3419140734566292106717993) ^ 1709570367283146053358996 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419140734566292106717993) ^ 1139713578188764035572664 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419140734566292106717993) ^ 110294862405364261507032 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419140734566292106717993) ^ 7555561107292268424 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419140734566292106717993) ^ 394771579898385672 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419140734566292106717993) ^ 26244408983667048 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3860562815445919273144033 : Nat.Prime 3860562815445919273144033 := by
  apply lucas_primality 3860562815445919273144033 (7 : ZMod 3860562815445919273144033)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 2), (415409, 1), (182998620855997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 2), (415409, 1), (182998620855997, 1)] : List FactorBlock).map factorBlockValue).prod) = 3860562815445919273144033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_415409
      · exact prime_ninetyFiveCO_182998620855997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3860562815445919273144033) ^ 1930281407722959636572016 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3860562815445919273144033) ^ 1286854271815306424381344 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3860562815445919273144033) ^ 167850557193300837962784 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3860562815445919273144033) ^ 9293401961550951648 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3860562815445919273144033) ^ 21096130656 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_8137614402968274845209343 : Nat.Prime 8137614402968274845209343 := by
  apply lucas_primality 8137614402968274845209343 (5 : ZMod 8137614402968274845209343)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (18047, 1), (17342781035348459461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (18047, 1), (17342781035348459461, 1)] : List FactorBlock).map factorBlockValue).prod) = 8137614402968274845209343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_18047
      · exact prime_ninetyFiveCO_17342781035348459461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8137614402968274845209343) ^ 4068807201484137422604671 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8137614402968274845209343) ^ 625970338689867295785334 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8137614402968274845209343) ^ 450912306919059945986 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8137614402968274845209343) ^ 469222 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_19864760167981628831549231 : Nat.Prime 19864760167981628831549231 := by
  apply lucas_primality 19864760167981628831549231 (11 : ZMod 19864760167981628831549231)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1933, 1), (1027664778478097715031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1933, 1), (1027664778478097715031, 1)] : List FactorBlock).map factorBlockValue).prod) = 19864760167981628831549231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_1933
      · exact prime_ninetyFiveCO_1027664778478097715031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19864760167981628831549231) ^ 9932380083990814415774615 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 19864760167981628831549231) ^ 3972952033596325766309846 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 19864760167981628831549231) ^ 10276647784780977150310 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (11 : ZMod 19864760167981628831549231) ^ 19330 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_29611219085095736729127169 : Nat.Prime 29611219085095736729127169 := by
  apply lucas_primality 29611219085095736729127169 (13 : ZMod 29611219085095736729127169)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (11, 1), (31, 1), (46334209, 1), (813425308093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (11, 1), (31, 1), (46334209, 1), (813425308093, 1)] : List FactorBlock).map factorBlockValue).prod) = 29611219085095736729127169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_31
      · exact prime_ninetyFiveCO_46334209
      · exact prime_ninetyFiveCO_813425308093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 29611219085095736729127169) ^ 14805609542547868364563584 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 29611219085095736729127169) ^ 9870406361698578909709056 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 29611219085095736729127169) ^ 2691929007735976066284288 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 29611219085095736729127169) ^ 955200615648249571907328 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 29611219085095736729127169) ^ 639078981257578752 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 29611219085095736729127169) ^ 36403119979776 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_38163558949972181248243069 : Nat.Prime 38163558949972181248243069 := by
  apply lucas_primality 38163558949972181248243069 (2 : ZMod 38163558949972181248243069)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (457, 1), (15383, 1), (1129859, 1), (3255225067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (457, 1), (15383, 1), (1129859, 1), (3255225067, 1)] : List FactorBlock).map factorBlockValue).prod) = 38163558949972181248243069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_457
      · exact prime_ninetyFiveCO_15383
      · exact prime_ninetyFiveCO_1129859
      · exact prime_ninetyFiveCO_3255225067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38163558949972181248243069) ^ 19081779474986090624121534 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38163558949972181248243069) ^ 12721186316657393749414356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38163558949972181248243069) ^ 930818510974931249957148 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38163558949972181248243069) ^ 83508881728604335335324 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38163558949972181248243069) ^ 2480891825389857716196 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38163558949972181248243069) ^ 33777275704288925652 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38163558949972181248243069) ^ 11723785042348404 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_51029238523293107411894299 : Nat.Prime 51029238523293107411894299 := by
  apply lucas_primality 51029238523293107411894299 (2 : ZMod 51029238523293107411894299)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1543259, 1), (1836994111641990079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1543259, 1), (1836994111641990079, 1)] : List FactorBlock).map factorBlockValue).prod) = 51029238523293107411894299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_1543259
      · exact prime_ninetyFiveCO_1836994111641990079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51029238523293107411894299) ^ 25514619261646553705947149 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51029238523293107411894299) ^ 17009746174431035803964766 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51029238523293107411894299) ^ 33065894009555821422 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51029238523293107411894299) ^ 27778662 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_70153250462066289452579233 : Nat.Prime 70153250462066289452579233 := by
  apply lucas_primality 70153250462066289452579233 (5 : ZMod 70153250462066289452579233)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (37, 1), (109, 1), (125471, 1), (206303665293767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (37, 1), (109, 1), (125471, 1), (206303665293767, 1)] : List FactorBlock).map factorBlockValue).prod) = 70153250462066289452579233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_7
      · exact prime_ninetyFiveCO_37
      · exact prime_ninetyFiveCO_109
      · exact prime_ninetyFiveCO_125471
      · exact prime_ninetyFiveCO_206303665293767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 70153250462066289452579233) ^ 35076625231033144726289616 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70153250462066289452579233) ^ 23384416820688763150859744 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70153250462066289452579233) ^ 10021892923152327064654176 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70153250462066289452579233) ^ 1896033796272061877096736 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70153250462066289452579233) ^ 643607802404277884886048 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70153250462066289452579233) ^ 559119242391200272992 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70153250462066289452579233) ^ 340048492896 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_226899705029834604875917883 : Nat.Prime 226899705029834604875917883 := by
  apply lucas_primality 226899705029834604875917883 (2 : ZMod 226899705029834604875917883)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (491, 1), (310758823, 1), (743530820875537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (491, 1), (310758823, 1), (743530820875537, 1)] : List FactorBlock).map factorBlockValue).prod) = 226899705029834604875917883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_491
      · exact prime_ninetyFiveCO_310758823
      · exact prime_ninetyFiveCO_743530820875537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 226899705029834604875917883) ^ 113449852514917302437958941 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 226899705029834604875917883) ^ 462117525519011415225902 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 226899705029834604875917883) ^ 730147266099777334 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 226899705029834604875917883) ^ 305165164186 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_332293946715290323708814651 : Nat.Prime 332293946715290323708814651 := by
  apply lucas_primality 332293946715290323708814651 (10 : ZMod 332293946715290323708814651)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (1163, 1), (37799, 1), (13743574954102699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (1163, 1), (37799, 1), (13743574954102699, 1)] : List FactorBlock).map factorBlockValue).prod) = 332293946715290323708814651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_11
      · exact prime_ninetyFiveCO_1163
      · exact prime_ninetyFiveCO_37799
      · exact prime_ninetyFiveCO_13743574954102699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 332293946715290323708814651) ^ 166146973357645161854407325 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 332293946715290323708814651) ^ 66458789343058064741762930 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 332293946715290323708814651) ^ 30208540610480938518983150 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 332293946715290323708814651) ^ 285721364329570355725550 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 332293946715290323708814651) ^ 8791077719391791415350 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (10 : ZMod 332293946715290323708814651) ^ 24178130350 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_374384513299227098045264507 : Nat.Prime 374384513299227098045264507 := by
  apply lucas_primality 374384513299227098045264507 (2 : ZMod 374384513299227098045264507)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2371, 1), (1796983, 1), (43935174666596921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2371, 1), (1796983, 1), (43935174666596921, 1)] : List FactorBlock).map factorBlockValue).prod) = 374384513299227098045264507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_2371
      · exact prime_ninetyFiveCO_1796983
      · exact prime_ninetyFiveCO_43935174666596921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 374384513299227098045264507) ^ 187192256649613549022632253 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 374384513299227098045264507) ^ 157901523955810669778686 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 374384513299227098045264507) ^ 208340598269002599382 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 374384513299227098045264507) ^ 8521293386 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_389983868020028227130483861 : Nat.Prime 389983868020028227130483861 := by
  apply lucas_primality 389983868020028227130483861 (3 : ZMod 389983868020028227130483861)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (825029, 1), (122258063, 1), (8405084533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (825029, 1), (122258063, 1), (8405084533, 1)] : List FactorBlock).map factorBlockValue).prod) = 389983868020028227130483861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_23
      · exact prime_ninetyFiveCO_825029
      · exact prime_ninetyFiveCO_122258063
      · exact prime_ninetyFiveCO_8405084533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 389983868020028227130483861) ^ 194991934010014113565241930 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 389983868020028227130483861) ^ 77996773604005645426096772 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 389983868020028227130483861) ^ 16955820348696879440455820 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 389983868020028227130483861) ^ 472691103003686206340 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 389983868020028227130483861) ^ 3189841704101170220 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 389983868020028227130483861) ^ 46398565831060420 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1157890247317197210449271671 : Nat.Prime 1157890247317197210449271671 := by
  apply lucas_primality 1157890247317197210449271671 (7 : ZMod 1157890247317197210449271671)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (149, 1), (22669, 1), (1013178137, 1), (33834748711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (149, 1), (22669, 1), (1013178137, 1), (33834748711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157890247317197210449271671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_149
      · exact prime_ninetyFiveCO_22669
      · exact prime_ninetyFiveCO_1013178137
      · exact prime_ninetyFiveCO_33834748711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1157890247317197210449271671) ^ 578945123658598605224635835 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157890247317197210449271671) ^ 231578049463439442089854334 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157890247317197210449271671) ^ 7771075485350316848652830 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157890247317197210449271671) ^ 51078135220662455796430 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157890247317197210449271671) ^ 1142829878609191910 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157890247317197210449271671) ^ 34221925429602970 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_1477833605128528018599728317 : Nat.Prime 1477833605128528018599728317 := by
  apply lucas_primality 1477833605128528018599728317 (2 : ZMod 1477833605128528018599728317)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (293, 1), (22753207163, 1), (18472856243827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (293, 1), (22753207163, 1), (18472856243827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128528018599728317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_293
      · exact prime_ninetyFiveCO_22753207163
      · exact prime_ninetyFiveCO_18472856243827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1477833605128528018599728317) ^ 738916802564264009299864158 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1477833605128528018599728317) ^ 492611201709509339533242772 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1477833605128528018599728317) ^ 5043800700097365251193612 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1477833605128528018599728317) ^ 64950562553295732 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1477833605128528018599728317) ^ 80000276385108 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_3119870944160225817043870889 : Nat.Prime 3119870944160225817043870889 := by
  apply lucas_primality 3119870944160225817043870889 (3 : ZMod 3119870944160225817043870889)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (389983868020028227130483861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (389983868020028227130483861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3119870944160225817043870889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_389983868020028227130483861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3119870944160225817043870889) ^ 1559935472080112908521935444 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119870944160225817043870889) ^ 8 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_6239741888320451634087741781 : Nat.Prime 6239741888320451634087741781 := by
  apply lucas_primality 6239741888320451634087741781 (14 : ZMod 6239741888320451634087741781)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (1291, 1), (8950486112287993278377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (1291, 1), (8950486112287993278377, 1)] : List FactorBlock).map factorBlockValue).prod) = 6239741888320451634087741781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_1291
      · exact prime_ninetyFiveCO_8950486112287993278377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 6239741888320451634087741781) ^ 3119870944160225817043870890 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 6239741888320451634087741781) ^ 2079913962773483878029247260 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 6239741888320451634087741781) ^ 1247948377664090326817548356 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 6239741888320451634087741781) ^ 4833262500635516370323580 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (14 : ZMod 6239741888320451634087741781) ^ 697140 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_8639642614597548416429180927 : Nat.Prime 8639642614597548416429180927 := by
  apply lucas_primality 8639642614597548416429180927 (5 : ZMod 8639642614597548416429180927)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (332293946715290323708814651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (332293946715290323708814651, 1)] : List FactorBlock).map factorBlockValue).prod) = 8639642614597548416429180927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_13
      · exact prime_ninetyFiveCO_332293946715290323708814651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8639642614597548416429180927) ^ 4319821307298774208214590463 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8639642614597548416429180927) ^ 664587893430580647417629302 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8639642614597548416429180927) ^ 26 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_12479483776640903268175483559 : Nat.Prime 12479483776640903268175483559 := by
  apply lucas_primality 12479483776640903268175483559 (13 : ZMod 12479483776640903268175483559)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (47, 1), (10007077, 1), (20618963, 1), (37848248371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (47, 1), (10007077, 1), (20618963, 1), (37848248371, 1)] : List FactorBlock).map factorBlockValue).prod) = 12479483776640903268175483559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_17
      · exact prime_ninetyFiveCO_47
      · exact prime_ninetyFiveCO_10007077
      · exact prime_ninetyFiveCO_20618963
      · exact prime_ninetyFiveCO_37848248371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 12479483776640903268175483559) ^ 6239741888320451634087741779 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 12479483776640903268175483559) ^ 734087280978876662833851974 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 12479483776640903268175483559) ^ 265520931417891558897350714 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 12479483776640903268175483559) ^ 1247065829176781918254 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 12479483776640903268175483559) ^ 605243036550427064066 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (13 : ZMod 12479483776640903268175483559) ^ 329724209541039298 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_37438451329922709804526450693 : Nat.Prime 37438451329922709804526450693 := by
  apply lucas_primality 37438451329922709804526450693 (2 : ZMod 37438451329922709804526450693)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (32983, 1), (5472017, 1), (421614151954741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (32983, 1), (5472017, 1), (421614151954741, 1)] : List FactorBlock).map factorBlockValue).prod) = 37438451329922709804526450693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_41
      · exact prime_ninetyFiveCO_32983
      · exact prime_ninetyFiveCO_5472017
      · exact prime_ninetyFiveCO_421614151954741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37438451329922709804526450693) ^ 18719225664961354902263225346 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37438451329922709804526450693) ^ 12479483776640903268175483564 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37438451329922709804526450693) ^ 913132959266407556207962212 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37438451329922709804526450693) ^ 1135083265012967583437724 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37438451329922709804526450693) ^ 6841800990370225422276 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37438451329922709804526450693) ^ 88797900061812 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_112315353989768129413579352011 : Nat.Prime 112315353989768129413579352011 := by
  apply lucas_primality 112315353989768129413579352011 (2 : ZMod 112315353989768129413579352011)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (271, 1), (991, 1), (480703110407751835543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (271, 1), (991, 1), (480703110407751835543, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_5
      · exact prime_ninetyFiveCO_29
      · exact prime_ninetyFiveCO_271
      · exact prime_ninetyFiveCO_991
      · exact prime_ninetyFiveCO_480703110407751835543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112315353989768129413579352011) ^ 56157676994884064706789676005 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315353989768129413579352011) ^ 37438451329922709804526450670 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315353989768129413579352011) ^ 22463070797953625882715870402 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315353989768129413579352011) ^ 3872943241026487221157908690 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315353989768129413579352011) ^ 414447800700251400050108310 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315353989768129413579352011) ^ 113335372340835650265973110 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (2 : ZMod 112315353989768129413579352011) ^ 233648070 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem prime_ninetyFiveCO_112315353989768129413579352047 : Nat.Prime 112315353989768129413579352047 := by
  apply lucas_primality 112315353989768129413579352047 (3 : ZMod 112315353989768129413579352047)
  · rw [← ninetyFiveCOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (60427, 1), (1039838509, 1), (5049390257993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (60427, 1), (1039838509, 1), (5049390257993, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyFiveCO_2
      · exact prime_ninetyFiveCO_3
      · exact prime_ninetyFiveCO_59
      · exact prime_ninetyFiveCO_60427
      · exact prime_ninetyFiveCO_1039838509
      · exact prime_ninetyFiveCO_5049390257993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112315353989768129413579352047) ^ 56157676994884064706789676023 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112315353989768129413579352047) ^ 37438451329922709804526450682 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112315353989768129413579352047) ^ 1903650067623188634128463594 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112315353989768129413579352047) ^ 1858694854779620524162698 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112315353989768129413579352047) ^ 108012304812389025894 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112315353989768129413579352047) ^ 22243349840503422 ≠ 1
      rw [← ninetyFiveCOFastPow_eq_pow]
      decide

private theorem phi_ninetyFiveCO_112315353989768129413579352000 : Nat.totient 112315353989768129413579352000 = 38456583811553794872360960000 := by
  rw [← show ((([(2, 6), (5, 3), (7, 1), (1097, 1), (2341, 1), (780985664076995921, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5, prime_ninetyFiveCO_7, prime_ninetyFiveCO_1097, prime_ninetyFiveCO_2341, prime_ninetyFiveCO_780985664076995921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352001 : Nat.totient 112315353989768129413579352001 = 74676159475715300333951962944 := by
  rw [← show ((([(3, 1), (373, 1), (91319077, 1), (1099126124436642227, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_373, prime_ninetyFiveCO_91319077, prime_ninetyFiveCO_1099126124436642227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352002 : Nat.totient 112315353989768129413579352002 = 53683847351107111206355750848 := by
  rw [← show ((([(2, 1), (23, 1), (1669, 1), (14074523, 1), (17176039, 1), (6051572759, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_23, prime_ninetyFiveCO_1669, prime_ninetyFiveCO_14074523, prime_ninetyFiveCO_17176039, prime_ninetyFiveCO_6051572759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352003 : Nat.totient 112315353989768129413579352003 = 112315292738951267115384120000 := by
  rw [← show ((([(1833751, 1), (64878580189, 1), (944055288377, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_1833751, prime_ninetyFiveCO_64878580189, prime_ninetyFiveCO_944055288377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352004 : Nat.totient 112315353989768129413579352004 = 37438451329922709804526450656 := by
  rw [← show ((([(2, 2), (3, 2), (3119870944160225817043870889, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_3119870944160225817043870889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352005 : Nat.totient 112315353989768129413579352005 = 83811679028031112445291397120 := by
  rw [← show ((([(5, 1), (17, 1), (131, 1), (769, 1), (176713, 1), (3724067, 1), (19931343937, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_5, prime_ninetyFiveCO_17, prime_ninetyFiveCO_131, prime_ninetyFiveCO_769, prime_ninetyFiveCO_176713, prime_ninetyFiveCO_3724067, prime_ninetyFiveCO_19931343937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352006 : Nat.totient 112315353989768129413579352006 = 54346139006617229876331225600 := by
  rw [← show ((([(2, 1), (31, 1), (2626695233, 1), (689664314617844861, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_31, prime_ninetyFiveCO_2626695233, prime_ninetyFiveCO_689664314617844861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352007 : Nat.totient 112315353989768129413579352007 = 62686245479167684142413273440 := by
  rw [← show ((([(3, 1), (7, 1), (43, 1), (44971, 1), (2765787662637864579139, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_7, prime_ninetyFiveCO_43, prime_ninetyFiveCO_44971, prime_ninetyFiveCO_2765787662637864579139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352008 : Nat.totient 112315353989768129413579352008 = 50739228517407799679307946080 := by
  rw [← show ((([(2, 3), (11, 2), (163, 1), (711829805238605494939787, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_11, prime_ninetyFiveCO_163, prime_ninetyFiveCO_711829805238605494939787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352009 : Nat.totient 112315353989768129413579352009 = 112315353987986392658827111440 := by
  rw [← show ((([(63037010189, 1), (1781736691715230381, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_63037010189, prime_ninetyFiveCO_1781736691715230381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352010 : Nat.totient 112315353989768129413579352010 = 28782194876286222703444358400 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (29, 1), (271, 1), (991, 1), (480703110407751835543, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_5, prime_ninetyFiveCO_29, prime_ninetyFiveCO_271, prime_ninetyFiveCO_991, prime_ninetyFiveCO_480703110407751835543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352011 : Nat.totient 112315353989768129413579352011 = 112315353989768129413579352010 := by
  rw [← show ((([(112315353989768129413579352011, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_112315353989768129413579352011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352012 : Nat.totient 112315353989768129413579352012 = 51733972209096687728653351488 := by
  rw [← show ((([(2, 2), (13, 1), (499, 1), (338750986003, 1), (12777758420423, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_13, prime_ninetyFiveCO_499, prime_ninetyFiveCO_338750986003, prime_ninetyFiveCO_12777758420423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352013 : Nat.totient 112315353989768129413579352013 = 74876880184649217446538412800 := by
  rw [← show ((([(3, 3), (3994189, 1), (20081041, 1), (51863345973731, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_3994189, prime_ninetyFiveCO_20081041, prime_ninetyFiveCO_51863345973731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352014 : Nat.totient 112315353989768129413579352014 = 48135151709894433972025274400 := by
  rw [← show ((([(2, 1), (7, 1), (7832040574541, 1), (1024321210881061, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_7, prime_ninetyFiveCO_7832040574541, prime_ninetyFiveCO_1024321210881061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352015 : Nat.totient 112315353989768129413579352015 = 89846190943294228726369665024 := by
  rw [← show ((([(5, 1), (19697, 1), (58727, 1), (149325493, 1), (130046080609, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_5, prime_ninetyFiveCO_19697, prime_ninetyFiveCO_58727, prime_ninetyFiveCO_149325493, prime_ninetyFiveCO_130046080609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352016 : Nat.totient 112315353989768129413579352016 = 35346955304726928907974461952 := by
  rw [← show ((([(2, 4), (3, 1), (19, 1), (293, 1), (22753207163, 1), (18472856243827, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_19, prime_ninetyFiveCO_293, prime_ninetyFiveCO_22753207163, prime_ninetyFiveCO_18472856243827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352017 : Nat.totient 112315353989768129413579352017 = 112285742770683033676850221056 := by
  rw [← show ((([(3793, 1), (29611219085095736729127169, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3793, prime_ninetyFiveCO_29611219085095736729127169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352018 : Nat.totient 112315353989768129413579352018 = 56157676992812026725569723716 := by
  rw [← show ((([(2, 1), (27102629507, 1), (2072037954117322787, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_27102629507, prime_ninetyFiveCO_2072037954117322787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352019 : Nat.totient 112315353989768129413579352019 = 67047137488709377751470118400 := by
  rw [← show ((([(3, 1), (11, 1), (67, 1), (9871, 1), (13411109, 1), (14427037, 1), (26597903, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_11, prime_ninetyFiveCO_67, prime_ninetyFiveCO_9871, prime_ninetyFiveCO_13411109, prime_ninetyFiveCO_14427037, prime_ninetyFiveCO_26597903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352020 : Nat.totient 112315353989768129413579352020 = 44925851767746594679995098880 := by
  rw [← show ((([(2, 2), (5, 1), (167107, 1), (2141203, 1), (15694831186716281, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5, prime_ninetyFiveCO_167107, prime_ninetyFiveCO_2141203, prime_ninetyFiveCO_15694831186716281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352021 : Nat.totient 112315353989768129413579352021 = 95813808339269466871500257280 := by
  rw [← show ((([(7, 1), (211, 1), (403057, 1), (188665359233372641889, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_7, prime_ninetyFiveCO_211, prime_ninetyFiveCO_403057, prime_ninetyFiveCO_188665359233372641889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352022 : Nat.totient 112315353989768129413579352022 = 34486478208006560058825815040 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (47, 1), (10007077, 1), (20618963, 1), (37848248371, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_17, prime_ninetyFiveCO_47, prime_ninetyFiveCO_10007077, prime_ninetyFiveCO_20618963, prime_ninetyFiveCO_37848248371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352023 : Nat.totient 112315353989768129413579352023 = 109279803881928442209926567040 := by
  rw [← show ((([(37, 1), (14381973219409, 1), (211066316250331, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_37, prime_ninetyFiveCO_14381973219409, prime_ninetyFiveCO_211066316250331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352024 : Nat.totient 112315353989768129413579352024 = 56148948890950664833248726432 := by
  rw [← show ((([(2, 3), (7079, 1), (70619, 1), (28083786804509413303, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_7079, prime_ninetyFiveCO_70619, prime_ninetyFiveCO_28083786804509413303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352025 : Nat.totient 112315353989768129413579352025 = 52811046602730259624230912000 := by
  rw [← show ((([(3, 1), (5, 2), (13, 1), (23, 1), (673, 1), (13929121, 1), (534278752487681, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_5, prime_ninetyFiveCO_13, prime_ninetyFiveCO_23, prime_ninetyFiveCO_673, prime_ninetyFiveCO_13929121, prime_ninetyFiveCO_534278752487681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352026 : Nat.totient 112315353989768129413579352026 = 55959236567981374570271088816 := by
  rw [← show ((([(2, 1), (283, 1), (20622299, 1), (80898887, 1), (118944146147, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_283, prime_ninetyFiveCO_20622299, prime_ninetyFiveCO_80898887, prime_ninetyFiveCO_118944146147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352027 : Nat.totient 112315353989768129413579352027 = 111203320781702744596290637600 := by
  rw [← show ((([(101, 1), (452316019283, 1), (2458531558493669, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_101, prime_ninetyFiveCO_452316019283, prime_ninetyFiveCO_2458531558493669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352028 : Nat.totient 112315353989768129413579352028 = 31638127884369329761950220800 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (71, 1), (441533777957, 1), (42651819450761, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_7, prime_ninetyFiveCO_71, prime_ninetyFiveCO_441533777957, prime_ninetyFiveCO_42651819450761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352029 : Nat.totient 112315353989768129413579352029 = 112315353989718060681761351520 := by
  rw [← show ((([(2243323975141, 1), (50066488494025369, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2243323975141, prime_ninetyFiveCO_50066488494025369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352030 : Nat.totient 112315353989768129413579352030 = 40841944650519564334023346560 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (18234763, 1), (3209669423, 1), (17445604277, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5, prime_ninetyFiveCO_11, prime_ninetyFiveCO_18234763, prime_ninetyFiveCO_3209669423, prime_ninetyFiveCO_17445604277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352031 : Nat.totient 112315353989768129413579352031 = 74876902659845419609052901348 := by
  rw [← show ((([(3, 2), (12479483776640903268175483559, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_12479483776640903268175483559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352032 : Nat.totient 112315353989768129413579352032 = 56157654587703143325195045888 := by
  rw [← show ((([(2, 5), (3184969, 1), (11760557, 1), (93703551406147, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3184969, prime_ninetyFiveCO_11760557, prime_ninetyFiveCO_93703551406147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352033 : Nat.totient 112315353989768129413579352033 = 112245200739306063124126771200 := by
  rw [← show ((([(1601, 1), (70153250462066289452579233, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_1601, prime_ninetyFiveCO_70153250462066289452579233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352034 : Nat.totient 112315353989768129413579352034 = 37437142613478136004064809712 := by
  rw [← show ((([(2, 1), (3, 1), (28607, 1), (654358222286900230791877, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_28607, prime_ninetyFiveCO_654358222286900230791877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352035 : Nat.totient 112315353989768129413579352035 = 71182197004501182079714590720 := by
  rw [← show ((([(5, 1), (7, 2), (19, 2), (41, 1), (72647, 1), (426348071307079169, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_5, prime_ninetyFiveCO_7, prime_ninetyFiveCO_19, prime_ninetyFiveCO_41, prime_ninetyFiveCO_72647, prime_ninetyFiveCO_426348071307079169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352036 : Nat.totient 112315353989768129413579352036 = 56157676993191469901025525408 := by
  rw [← show ((([(2, 2), (33178454173, 1), (846297369703621133, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_33178454173, prime_ninetyFiveCO_846297369703621133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352037 : Nat.totient 112315353989768129413579352037 = 72461232366198100721084329920 := by
  rw [← show ((([(3, 1), (31, 1), (278269, 1), (2793859, 1), (1553412766166879, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_31, prime_ninetyFiveCO_278269, prime_ninetyFiveCO_2793859, prime_ninetyFiveCO_1553412766166879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352038 : Nat.totient 112315353989768129413579352038 = 51837855687585290498575085400 := by
  rw [← show ((([(2, 1), (13, 2), (332293946715290323708814651, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_13, prime_ninetyFiveCO_332293946715290323708814651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352039 : Nat.totient 112315353989768129413579352039 = 101912686997861638887229928960 := by
  rw [← show ((([(17, 1), (29, 2), (677, 1), (11603941865665812426131, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_17, prime_ninetyFiveCO_29, prime_ninetyFiveCO_677, prime_ninetyFiveCO_11603941865665812426131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352040 : Nat.totient 112315353989768129413579352040 = 29927561403935117365040263680 := by
  rw [← show ((([(2, 3), (3, 5), (5, 1), (1291, 1), (8950486112287993278377, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_5, prime_ninetyFiveCO_1291, prime_ninetyFiveCO_8950486112287993278377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352041 : Nat.totient 112315353989768129413579352041 = 100169162063765014599396388800 := by
  rw [← show ((([(11, 1), (53, 1), (10891, 1), (17688981080695948046797, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_11, prime_ninetyFiveCO_53, prime_ninetyFiveCO_10891, prime_ninetyFiveCO_17688981080695948046797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352042 : Nat.totient 112315353989768129413579352042 = 47346050862174561997016580480 := by
  rw [← show ((([(2, 1), (7, 1), (61, 1), (2151974037959, 1), (61114495635497, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_7, prime_ninetyFiveCO_61, prime_ninetyFiveCO_2151974037959, prime_ninetyFiveCO_61114495635497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352043 : Nat.totient 112315353989768129413579352043 = 74876530397781494693685104640 := by
  rw [← show ((([(3, 1), (210809, 1), (4385489, 1), (40495866990652081, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_210809, prime_ninetyFiveCO_4385489, prime_ninetyFiveCO_40495866990652081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352044 : Nat.totient 112315353989768129413579352044 = 56078390733171007971776025600 := by
  rw [← show ((([(2, 2), (757, 1), (10993, 1), (47846059981, 1), (70521387931, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_757, prime_ninetyFiveCO_10993, prime_ninetyFiveCO_47846059981, prime_ninetyFiveCO_70521387931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352045 : Nat.totient 112315353989768129413579352045 = 89848446138255473146803480064 := by
  rw [← show ((([(5, 1), (23417, 1), (959263389757596014976977, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_5, prime_ninetyFiveCO_23417, prime_ninetyFiveCO_959263389757596014976977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352046 : Nat.totient 112315353989768129413579352046 = 36803292208130362655479493376 := by
  rw [← show ((([(2, 1), (3, 1), (59, 1), (60427, 1), (1039838509, 1), (5049390257993, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_59, prime_ninetyFiveCO_60427, prime_ninetyFiveCO_1039838509, prime_ninetyFiveCO_5049390257993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352047 : Nat.totient 112315353989768129413579352047 = 112315353989768129413579352046 := by
  rw [← show ((([(112315353989768129413579352047, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_112315353989768129413579352047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352048 : Nat.totient 112315353989768129413579352048 = 53716038864661130226878822400 := by
  rw [← show ((([(2, 4), (23, 1), (5596040111881, 1), (54539417190481, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_23, prime_ninetyFiveCO_5596040111881, prime_ninetyFiveCO_54539417190481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352049 : Nat.totient 112315353989768129413579352049 = 64180047361122876583957851360 := by
  rw [← show ((([(3, 2), (7, 1), (414283, 1), (4303298461831613127181, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_7, prime_ninetyFiveCO_414283, prime_ninetyFiveCO_4303298461831613127181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352050 : Nat.totient 112315353989768129413579352050 = 43445668224705318296733818880 := by
  rw [← show ((([(2, 1), (5, 2), (43, 1), (113, 1), (919, 1), (1938637, 1), (259483781416633, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5, prime_ninetyFiveCO_43, prime_ninetyFiveCO_113, prime_ninetyFiveCO_919, prime_ninetyFiveCO_1938637, prime_ninetyFiveCO_259483781416633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352051 : Nat.totient 112315353989768129413579352051 = 103675711375170580997150171112 := by
  rw [← show ((([(13, 1), (8639642614597548416429180927, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_13, prime_ninetyFiveCO_8639642614597548416429180927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352052 : Nat.totient 112315353989768129413579352052 = 34034370951372826855876644960 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (58199, 1), (14620077559096887717739, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_11, prime_ninetyFiveCO_58199, prime_ninetyFiveCO_14620077559096887717739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352053 : Nat.totient 112315353989768129413579352053 = 112315353982802573621000790528 := by
  rw [← show ((([(16124392309, 1), (6965555776454169217, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_16124392309, prime_ninetyFiveCO_6965555776454169217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352054 : Nat.totient 112315353989768129413579352054 = 52443959305768046542142959104 := by
  rw [← show ((([(2, 1), (19, 1), (83, 1), (449, 1), (79310575314810852421699, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_19, prime_ninetyFiveCO_83, prime_ninetyFiveCO_449, prime_ninetyFiveCO_79310575314810852421699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352055 : Nat.totient 112315353989768129413579352055 = 59901512057575715441241954432 := by
  rw [← show ((([(3, 1), (5, 1), (5957899, 1), (3746931709, 1), (335412278407, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_5, prime_ninetyFiveCO_5957899, prime_ninetyFiveCO_3746931709, prime_ninetyFiveCO_335412278407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352056 : Nat.totient 112315353989768129413579352056 = 45303648820165116894190382592 := by
  rw [← show ((([(2, 3), (7, 1), (17, 1), (1937927, 1), (60878615662232024639, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_7, prime_ninetyFiveCO_17, prime_ninetyFiveCO_1937927, prime_ninetyFiveCO_60878615662232024639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352057 : Nat.totient 112315353989768129413579352057 = 110903248866392250773504788512 := by
  rw [← show ((([(107, 1), (307, 1), (3419140734566292106717993, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_107, prime_ninetyFiveCO_307, prime_ninetyFiveCO_3419140734566292106717993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352058 : Nat.totient 112315353989768129413579352058 = 37438451329922709804526450680 := by
  rw [← show ((([(2, 1), (3, 2), (6239741888320451634087741781, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_6239741888320451634087741781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352059 : Nat.totient 112315353989768129413579352059 = 112195662528340070247792032640 := by
  rw [← show ((([(941, 1), (418637, 1), (1699543, 1), (167756648152789, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_941, prime_ninetyFiveCO_418637, prime_ninetyFiveCO_1699543, prime_ninetyFiveCO_167756648152789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352060 : Nat.totient 112315353989768129413579352060 = 42673647355759769752953538560 := by
  rw [← show ((([(2, 2), (5, 1), (37, 1), (79, 1), (89, 1), (1395659, 1), (15467174742839011, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5, prime_ninetyFiveCO_37, prime_ninetyFiveCO_79, prime_ninetyFiveCO_89, prime_ninetyFiveCO_1395659, prime_ninetyFiveCO_15467174742839011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352061 : Nat.totient 112315353989768129413579352061 = 73845913814798236500423754800 := by
  rw [← show ((([(3, 1), (139, 1), (151, 1), (1783717724995126485517483, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_139, prime_ninetyFiveCO_151, prime_ninetyFiveCO_1783717724995126485517483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352062 : Nat.totient 112315353989768129413579352062 = 55910102720039607886810855488 := by
  rw [← show ((([(2, 1), (227, 1), (304477, 1), (812510132307383976889, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_227, prime_ninetyFiveCO_304477, prime_ninetyFiveCO_812510132307383976889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352063 : Nat.totient 112315353989768129413579352063 = 87461731271128666617049707360 := by
  rw [← show ((([(7, 1), (11, 1), (1543, 1), (13036867, 1), (72511893176675599, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_7, prime_ninetyFiveCO_11, prime_ninetyFiveCO_1543, prime_ninetyFiveCO_13036867, prime_ninetyFiveCO_72511893176675599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352064 : Nat.totient 112315353989768129413579352064 = 34294029856748443101081894912 := by
  rw [← show ((([(2, 11), (3, 1), (13, 1), (157, 1), (773, 1), (11586851062557052067, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_13, prime_ninetyFiveCO_157, prime_ninetyFiveCO_773, prime_ninetyFiveCO_11586851062557052067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352065 : Nat.totient 112315353989768129413579352065 = 89826595030444883011776011520 := by
  rw [← show ((([(5, 1), (3511, 1), (930737, 1), (6874028326989678859, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_5, prime_ninetyFiveCO_3511, prime_ninetyFiveCO_930737, prime_ninetyFiveCO_6874028326989678859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352066 : Nat.totient 112315353989768129413579352066 = 56093337330949209229427905920 := by
  rw [← show ((([(2, 1), (883, 1), (75709, 1), (3010712879, 1), (279017588441, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_883, prime_ninetyFiveCO_75709, prime_ninetyFiveCO_3010712879, prime_ninetyFiveCO_279017588441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352067 : Nat.totient 112315353989768129413579352067 = 74189958598745920346584524192 := by
  rw [← show ((([(3, 3), (109, 1), (38163558949972181248243069, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_109, prime_ninetyFiveCO_38163558949972181248243069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352068 : Nat.totient 112315353989768129413579352068 = 52471798384601705689104537600 := by
  rw [← show ((([(2, 2), (29, 1), (31, 1), (156241, 1), (11003707877, 1), (18167090719, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_29, prime_ninetyFiveCO_31, prime_ninetyFiveCO_156241, prime_ninetyFiveCO_11003707877, prime_ninetyFiveCO_18167090719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352069 : Nat.totient 112315353989768129413579352069 = 109748079717496593096938541696 := by
  rw [← show ((([(47, 1), (619, 1), (3860562815445919273144033, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_47, prime_ninetyFiveCO_619, prime_ninetyFiveCO_3860562815445919273144033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352070 : Nat.totient 112315353989768129413579352070 = 25671243131933883125692538880 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (30643, 1), (114551507561, 1), (152365887329, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_5, prime_ninetyFiveCO_7, prime_ninetyFiveCO_30643, prime_ninetyFiveCO_114551507561, prime_ninetyFiveCO_152365887329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352071 : Nat.totient 112315353989768129413579352071 = 105959561468626879237142424000 := by
  rw [← show ((([(23, 3), (73, 1), (125551, 1), (1007192738240212631, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_23, prime_ninetyFiveCO_73, prime_ninetyFiveCO_125551, prime_ninetyFiveCO_1007192738240212631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352072 : Nat.totient 112315353989768129413579352072 = 56157676994575894993898772816 := by
  rw [← show ((([(2, 3), (182230139683, 1), (77042245992586123, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_182230139683, prime_ninetyFiveCO_77042245992586123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352073 : Nat.totient 112315353989768129413579352073 = 66763306392910779034884418560 := by
  rw [← show ((([(3, 1), (17, 1), (19, 1), (19163450861, 1), (6048415751944997, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_17, prime_ninetyFiveCO_19, prime_ninetyFiveCO_19163450861, prime_ninetyFiveCO_6048415751944997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352074 : Nat.totient 112315353989768129413579352074 = 50853786030032969808766028800 := by
  rw [← show ((([(2, 1), (11, 1), (257, 1), (19864760167981628831549231, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_11, prime_ninetyFiveCO_257, prime_ninetyFiveCO_19864760167981628831549231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352075 : Nat.totient 112315353989768129413579352075 = 89809269331000831437267763200 := by
  rw [← show ((([(5, 2), (2203, 1), (40529, 1), (7775329, 1), (6471425586121, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_5, prime_ninetyFiveCO_2203, prime_ninetyFiveCO_40529, prime_ninetyFiveCO_7775329, prime_ninetyFiveCO_6471425586121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352076 : Nat.totient 112315353989768129413579352076 = 36524204297623465204183142400 := by
  rw [← show ((([(2, 2), (3, 2), (41, 1), (32983, 1), (5472017, 1), (421614151954741, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_41, prime_ninetyFiveCO_32983, prime_ninetyFiveCO_5472017, prime_ninetyFiveCO_421614151954741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352077 : Nat.totient 112315353989768129413579352077 = 88566442040130351277693351680 := by
  rw [← show ((([(7, 1), (13, 1), (311, 1), (6967, 1), (824886269, 1), (690553711699, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_7, prime_ninetyFiveCO_13, prime_ninetyFiveCO_311, prime_ninetyFiveCO_6967, prime_ninetyFiveCO_824886269, prime_ninetyFiveCO_690553711699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352078 : Nat.totient 112315353989768129413579352078 = 56157667416041867328407015520 := by
  rw [← show ((([(2, 1), (5862679, 1), (9578842197378376797841, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5862679, prime_ninetyFiveCO_9578842197378376797841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352079 : Nat.totient 112315353989768129413579352079 = 74876902659845419609052901384 := by
  rw [← show ((([(3, 1), (37438451329922709804526450693, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_37438451329922709804526450693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352080 : Nat.totient 112315353989768129413579352080 = 44926141595894610068394547200 := by
  rw [← show ((([(2, 4), (5, 1), (3586363891921, 1), (391466668520381, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5, prime_ninetyFiveCO_3586363891921, prime_ninetyFiveCO_391466668520381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352081 : Nat.totient 112315353989768129413579352081 = 112086605814620383214766141280 := by
  rw [← show ((([(491, 1), (10470476501657, 1), (21846968960363, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_491, prime_ninetyFiveCO_10470476501657, prime_ninetyFiveCO_21846968960363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352082 : Nat.totient 112315353989768129413579352082 = 37438451329793955403055802800 := by
  rw [← show ((([(2, 1), (3, 1), (290775460901, 1), (64376909959863047, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_290775460901, prime_ninetyFiveCO_64376909959863047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352083 : Nat.totient 112315353989768129413579352083 = 112315353989740722888360813520 := by
  rw [← show ((([(4098737535803, 1), (27402426481002761, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_4098737535803, prime_ninetyFiveCO_27402426481002761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352084 : Nat.totient 112315353989768129413579352084 = 48135151709896564352408415984 := by
  rw [← show ((([(2, 2), (7, 2), (20758187622967, 1), (27605373395987, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_7, prime_ninetyFiveCO_20758187622967, prime_ninetyFiveCO_27605373395987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352085 : Nat.totient 112315353989768129413579352085 = 54455929207160305170220291680 := by
  rw [← show ((([(3, 2), (5, 1), (11, 1), (226899705029834604875917883, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_5, prime_ninetyFiveCO_11, prime_ninetyFiveCO_226899705029834604875917883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352086 : Nat.totient 112315353989768129413579352086 = 54782420160782426257949290344 := by
  rw [← show ((([(2, 1), (67, 1), (103, 1), (8137614402968274845209343, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_67, prime_ninetyFiveCO_103, prime_ninetyFiveCO_8137614402968274845209343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352087 : Nat.totient 112315353989768129413579352087 = 111157463742450932203130080320 := by
  rw [← show ((([(97, 1), (1157890247317197210449271671, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_97, prime_ninetyFiveCO_1157890247317197210449271671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352088 : Nat.totient 112315353989768129413579352088 = 37438451275218513374359753248 := by
  rw [← show ((([(2, 3), (3, 1), (684379879, 1), (6838024553086457303, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_684379879, prime_ninetyFiveCO_6838024553086457303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352089 : Nat.totient 112315353989768129413579352089 = 112315343029391355778802915380 := by
  rw [← show ((([(10247399, 1), (10960376773634766189311, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_10247399, prime_ninetyFiveCO_10960376773634766189311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352090 : Nat.totient 112315353989768129413579352090 = 39030856046442461459496370176 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (17, 2), (57412567873, 1), (52070405925869, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_5, prime_ninetyFiveCO_13, prime_ninetyFiveCO_17, prime_ninetyFiveCO_57412567873, prime_ninetyFiveCO_52070405925869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352091 : Nat.totient 112315353989768129413579352091 = 64178738978730562430679121920 := by
  rw [← show ((([(3, 1), (7, 1), (44537, 1), (2988289, 1), (106965857, 1), (375691271, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_7, prime_ninetyFiveCO_44537, prime_ninetyFiveCO_2988289, prime_ninetyFiveCO_106965857, prime_ninetyFiveCO_375691271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352092 : Nat.totient 112315353989768129413579352092 = 53202009784627008669590219376 := by
  rw [← show ((([(2, 2), (19, 1), (1477833605128528018599728317, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_19, prime_ninetyFiveCO_1477833605128528018599728317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352093 : Nat.totient 112315353989768129413579352093 = 108579517884138578850240998400 := by
  rw [← show ((([(43, 1), (179, 1), (233, 1), (2539, 1), (53183401, 1), (463791639287, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_43, prime_ninetyFiveCO_179, prime_ninetyFiveCO_233, prime_ninetyFiveCO_2539, prime_ninetyFiveCO_53183401, prime_ninetyFiveCO_463791639287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352094 : Nat.totient 112315353989768129413579352094 = 35131103374670068210826135040 := by
  rw [← show ((([(2, 1), (3, 3), (23, 1), (53, 1), (10093, 1), (80831, 1), (2091430512780293, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_23, prime_ninetyFiveCO_53, prime_ninetyFiveCO_10093, prime_ninetyFiveCO_80831, prime_ninetyFiveCO_2091430512780293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352095 : Nat.totient 112315353989768129413579352095 = 89852262137444247101810364960 := by
  rw [← show ((([(5, 1), (4267631, 1), (5263592564107259011549, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_5, prime_ninetyFiveCO_4267631, prime_ninetyFiveCO_5263592564107259011549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352096 : Nat.totient 112315353989768129413579352096 = 50963600483798788914894028800 := by
  rw [← show ((([(2, 5), (11, 1), (577, 1), (143971, 1), (828204583, 1), (4637757143, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_11, prime_ninetyFiveCO_577, prime_ninetyFiveCO_143971, prime_ninetyFiveCO_828204583, prime_ninetyFiveCO_4637757143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352097 : Nat.totient 112315353989768129413579352097 = 70286026297686191689576497408 := by
  rw [← show ((([(3, 1), (29, 1), (37, 1), (1279, 1), (27280203713673317563397, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_3, prime_ninetyFiveCO_29, prime_ninetyFiveCO_37, prime_ninetyFiveCO_1279, prime_ninetyFiveCO_27280203713673317563397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352098 : Nat.totient 112315353989768129413579352098 = 48024036752945626537746167040 := by
  rw [← show ((([(2, 1), (7, 1), (443, 1), (19541, 1), (926745708477208575089, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_7, prime_ninetyFiveCO_443, prime_ninetyFiveCO_19541, prime_ninetyFiveCO_926745708477208575089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352099 : Nat.totient 112315353989768129413579352099 = 107161400898915525564978025800 := by
  rw [← show ((([(31, 1), (71, 1), (51029238523293107411894299, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_31, prime_ninetyFiveCO_71, prime_ninetyFiveCO_51029238523293107411894299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352100 : Nat.totient 112315353989768129413579352100 = 29950761063938167843621160480 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (374384513299227098045264507, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_2, prime_ninetyFiveCO_3, prime_ninetyFiveCO_5, prime_ninetyFiveCO_374384513299227098045264507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyFiveCO_112315353989768129413579352101 : Nat.totient 112315353989768129413579352101 = 112312876208134570641624227520 := by
  rw [← show ((([(45329, 1), (603333927499, 1), (4106815988831, 1)] : List FactorBlock).map factorBlockValue).prod) = 112315353989768129413579352101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyFiveCO_45329, prime_ninetyFiveCO_603333927499, prime_ninetyFiveCO_4106815988831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyFiveCO : certifiedKill 1 112315353989768129413579351999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyFiveCO_112315353989768129413579352000, phi_ninetyFiveCO_112315353989768129413579352001, phi_ninetyFiveCO_112315353989768129413579352002,
    phi_ninetyFiveCO_112315353989768129413579352003, phi_ninetyFiveCO_112315353989768129413579352004, phi_ninetyFiveCO_112315353989768129413579352005,
    phi_ninetyFiveCO_112315353989768129413579352006, phi_ninetyFiveCO_112315353989768129413579352007, phi_ninetyFiveCO_112315353989768129413579352008,
    phi_ninetyFiveCO_112315353989768129413579352009, phi_ninetyFiveCO_112315353989768129413579352010, phi_ninetyFiveCO_112315353989768129413579352011,
    phi_ninetyFiveCO_112315353989768129413579352012, phi_ninetyFiveCO_112315353989768129413579352013, phi_ninetyFiveCO_112315353989768129413579352014,
    phi_ninetyFiveCO_112315353989768129413579352015, phi_ninetyFiveCO_112315353989768129413579352016, phi_ninetyFiveCO_112315353989768129413579352017,
    phi_ninetyFiveCO_112315353989768129413579352018, phi_ninetyFiveCO_112315353989768129413579352019, phi_ninetyFiveCO_112315353989768129413579352020,
    phi_ninetyFiveCO_112315353989768129413579352021, phi_ninetyFiveCO_112315353989768129413579352022, phi_ninetyFiveCO_112315353989768129413579352023,
    phi_ninetyFiveCO_112315353989768129413579352024, phi_ninetyFiveCO_112315353989768129413579352025, phi_ninetyFiveCO_112315353989768129413579352026,
    phi_ninetyFiveCO_112315353989768129413579352027, phi_ninetyFiveCO_112315353989768129413579352028, phi_ninetyFiveCO_112315353989768129413579352029,
    phi_ninetyFiveCO_112315353989768129413579352030, phi_ninetyFiveCO_112315353989768129413579352031, phi_ninetyFiveCO_112315353989768129413579352032,
    phi_ninetyFiveCO_112315353989768129413579352033, phi_ninetyFiveCO_112315353989768129413579352034, phi_ninetyFiveCO_112315353989768129413579352035,
    phi_ninetyFiveCO_112315353989768129413579352036, phi_ninetyFiveCO_112315353989768129413579352037, phi_ninetyFiveCO_112315353989768129413579352038,
    phi_ninetyFiveCO_112315353989768129413579352039, phi_ninetyFiveCO_112315353989768129413579352040, phi_ninetyFiveCO_112315353989768129413579352041,
    phi_ninetyFiveCO_112315353989768129413579352042, phi_ninetyFiveCO_112315353989768129413579352043, phi_ninetyFiveCO_112315353989768129413579352044,
    phi_ninetyFiveCO_112315353989768129413579352045, phi_ninetyFiveCO_112315353989768129413579352046, phi_ninetyFiveCO_112315353989768129413579352047,
    phi_ninetyFiveCO_112315353989768129413579352048, phi_ninetyFiveCO_112315353989768129413579352049, phi_ninetyFiveCO_112315353989768129413579352050,
    phi_ninetyFiveCO_112315353989768129413579352051, phi_ninetyFiveCO_112315353989768129413579352052, phi_ninetyFiveCO_112315353989768129413579352053,
    phi_ninetyFiveCO_112315353989768129413579352054, phi_ninetyFiveCO_112315353989768129413579352055, phi_ninetyFiveCO_112315353989768129413579352056,
    phi_ninetyFiveCO_112315353989768129413579352057, phi_ninetyFiveCO_112315353989768129413579352058, phi_ninetyFiveCO_112315353989768129413579352059,
    phi_ninetyFiveCO_112315353989768129413579352060, phi_ninetyFiveCO_112315353989768129413579352061, phi_ninetyFiveCO_112315353989768129413579352062,
    phi_ninetyFiveCO_112315353989768129413579352063, phi_ninetyFiveCO_112315353989768129413579352064, phi_ninetyFiveCO_112315353989768129413579352065,
    phi_ninetyFiveCO_112315353989768129413579352066, phi_ninetyFiveCO_112315353989768129413579352067, phi_ninetyFiveCO_112315353989768129413579352068,
    phi_ninetyFiveCO_112315353989768129413579352069, phi_ninetyFiveCO_112315353989768129413579352070, phi_ninetyFiveCO_112315353989768129413579352071,
    phi_ninetyFiveCO_112315353989768129413579352072, phi_ninetyFiveCO_112315353989768129413579352073, phi_ninetyFiveCO_112315353989768129413579352074,
    phi_ninetyFiveCO_112315353989768129413579352075, phi_ninetyFiveCO_112315353989768129413579352076, phi_ninetyFiveCO_112315353989768129413579352077,
    phi_ninetyFiveCO_112315353989768129413579352078, phi_ninetyFiveCO_112315353989768129413579352079, phi_ninetyFiveCO_112315353989768129413579352080,
    phi_ninetyFiveCO_112315353989768129413579352081, phi_ninetyFiveCO_112315353989768129413579352082, phi_ninetyFiveCO_112315353989768129413579352083,
    phi_ninetyFiveCO_112315353989768129413579352084, phi_ninetyFiveCO_112315353989768129413579352085, phi_ninetyFiveCO_112315353989768129413579352086,
    phi_ninetyFiveCO_112315353989768129413579352087, phi_ninetyFiveCO_112315353989768129413579352088, phi_ninetyFiveCO_112315353989768129413579352089,
    phi_ninetyFiveCO_112315353989768129413579352090, phi_ninetyFiveCO_112315353989768129413579352091, phi_ninetyFiveCO_112315353989768129413579352092,
    phi_ninetyFiveCO_112315353989768129413579352093, phi_ninetyFiveCO_112315353989768129413579352094, phi_ninetyFiveCO_112315353989768129413579352095,
    phi_ninetyFiveCO_112315353989768129413579352096, phi_ninetyFiveCO_112315353989768129413579352097, phi_ninetyFiveCO_112315353989768129413579352098,
    phi_ninetyFiveCO_112315353989768129413579352099, phi_ninetyFiveCO_112315353989768129413579352100, phi_ninetyFiveCO_112315353989768129413579352101]

end TotientTailPeriodKiller
end Erdos249257
