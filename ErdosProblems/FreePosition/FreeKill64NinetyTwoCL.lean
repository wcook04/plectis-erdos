import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyTwoCLFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyTwoCLFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyTwoCLFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyTwoCLFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyTwoCLFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyTwoCLFastPow a n * ninetyTwoCLFastPow a n * a else ninetyTwoCLFastPow a n * ninetyTwoCLFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyTwoCL_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyTwoCL_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyTwoCL_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyTwoCL_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyTwoCL_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyTwoCL_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyTwoCL_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyTwoCL_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyTwoCL_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyTwoCL_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyTwoCL_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyTwoCL_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyTwoCL_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyTwoCL_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyTwoCL_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyTwoCL_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyTwoCL_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyTwoCL_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyTwoCL_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyTwoCL_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyTwoCL_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyTwoCL_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyTwoCL_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyTwoCL_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyTwoCL_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyTwoCL_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyTwoCL_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyTwoCL_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyTwoCL_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyTwoCL_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyTwoCL_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetyTwoCL_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyTwoCL_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyTwoCL_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetyTwoCL_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyTwoCL_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyTwoCL_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetyTwoCL_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyTwoCL_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetyTwoCL_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetyTwoCL_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetyTwoCL_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetyTwoCL_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyTwoCL_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyTwoCL_199 : Nat.Prime 199 := by norm_num

private theorem prime_ninetyTwoCL_211 : Nat.Prime 211 := by norm_num

private theorem prime_ninetyTwoCL_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetyTwoCL_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetyTwoCL_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetyTwoCL_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyTwoCL_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetyTwoCL_263 : Nat.Prime 263 := by norm_num

private theorem prime_ninetyTwoCL_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetyTwoCL_277 : Nat.Prime 277 := by norm_num

private theorem prime_ninetyTwoCL_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetyTwoCL_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetyTwoCL_317 : Nat.Prime 317 := by norm_num

private theorem prime_ninetyTwoCL_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyTwoCL_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetyTwoCL_349 : Nat.Prime 349 := by norm_num

private theorem prime_ninetyTwoCL_353 : Nat.Prime 353 := by norm_num

private theorem prime_ninetyTwoCL_359 : Nat.Prime 359 := by norm_num

private theorem prime_ninetyTwoCL_367 : Nat.Prime 367 := by norm_num

private theorem prime_ninetyTwoCL_373 : Nat.Prime 373 := by norm_num

private theorem prime_ninetyTwoCL_379 : Nat.Prime 379 := by norm_num

private theorem prime_ninetyTwoCL_397 : Nat.Prime 397 := by norm_num

private theorem prime_ninetyTwoCL_401 : Nat.Prime 401 := by norm_num

private theorem prime_ninetyTwoCL_409 : Nat.Prime 409 := by norm_num

private theorem prime_ninetyTwoCL_419 : Nat.Prime 419 := by norm_num

private theorem prime_ninetyTwoCL_433 : Nat.Prime 433 := by norm_num

private theorem prime_ninetyTwoCL_439 : Nat.Prime 439 := by norm_num

private theorem prime_ninetyTwoCL_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetyTwoCL_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetyTwoCL_457 : Nat.Prime 457 := by norm_num

private theorem prime_ninetyTwoCL_463 : Nat.Prime 463 := by norm_num

private theorem prime_ninetyTwoCL_479 : Nat.Prime 479 := by norm_num

private theorem prime_ninetyTwoCL_487 : Nat.Prime 487 := by norm_num

private theorem prime_ninetyTwoCL_499 : Nat.Prime 499 := by norm_num

private theorem prime_ninetyTwoCL_503 : Nat.Prime 503 := by norm_num

private theorem prime_ninetyTwoCL_509 : Nat.Prime 509 := by norm_num

private theorem prime_ninetyTwoCL_541 : Nat.Prime 541 := by norm_num

private theorem prime_ninetyTwoCL_547 : Nat.Prime 547 := by norm_num

private theorem prime_ninetyTwoCL_557 : Nat.Prime 557 := by norm_num

private theorem prime_ninetyTwoCL_563 : Nat.Prime 563 := by norm_num

private theorem prime_ninetyTwoCL_569 : Nat.Prime 569 := by norm_num

private theorem prime_ninetyTwoCL_577 : Nat.Prime 577 := by norm_num

private theorem prime_ninetyTwoCL_593 : Nat.Prime 593 := by norm_num

private theorem prime_ninetyTwoCL_599 : Nat.Prime 599 := by norm_num

private theorem prime_ninetyTwoCL_631 : Nat.Prime 631 := by norm_num

private theorem prime_ninetyTwoCL_643 : Nat.Prime 643 := by norm_num

private theorem prime_ninetyTwoCL_653 : Nat.Prime 653 := by norm_num

private theorem prime_ninetyTwoCL_659 : Nat.Prime 659 := by norm_num

private theorem prime_ninetyTwoCL_673 : Nat.Prime 673 := by norm_num

private theorem prime_ninetyTwoCL_691 : Nat.Prime 691 := by norm_num

private theorem prime_ninetyTwoCL_709 : Nat.Prime 709 := by norm_num

private theorem prime_ninetyTwoCL_787 : Nat.Prime 787 := by norm_num

private theorem prime_ninetyTwoCL_797 : Nat.Prime 797 := by norm_num

private theorem prime_ninetyTwoCL_809 : Nat.Prime 809 := by norm_num

private theorem prime_ninetyTwoCL_811 : Nat.Prime 811 := by norm_num

private theorem prime_ninetyTwoCL_821 : Nat.Prime 821 := by norm_num

private theorem prime_ninetyTwoCL_839 : Nat.Prime 839 := by norm_num

private theorem prime_ninetyTwoCL_863 : Nat.Prime 863 := by norm_num

private theorem prime_ninetyTwoCL_911 : Nat.Prime 911 := by norm_num

private theorem prime_ninetyTwoCL_929 : Nat.Prime 929 := by norm_num

private theorem prime_ninetyTwoCL_941 : Nat.Prime 941 := by norm_num

private theorem prime_ninetyTwoCL_967 : Nat.Prime 967 := by norm_num

private theorem prime_ninetyTwoCL_977 : Nat.Prime 977 := by norm_num

private theorem prime_ninetyTwoCL_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_ninetyTwoCL_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_ninetyTwoCL_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_ninetyTwoCL_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_ninetyTwoCL_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_ninetyTwoCL_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_ninetyTwoCL_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_ninetyTwoCL_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_ninetyTwoCL_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_ninetyTwoCL_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_ninetyTwoCL_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_ninetyTwoCL_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_ninetyTwoCL_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_ninetyTwoCL_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_ninetyTwoCL_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_ninetyTwoCL_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_ninetyTwoCL_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_ninetyTwoCL_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_ninetyTwoCL_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_ninetyTwoCL_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_ninetyTwoCL_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_ninetyTwoCL_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_ninetyTwoCL_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_ninetyTwoCL_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_ninetyTwoCL_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_ninetyTwoCL_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_ninetyTwoCL_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_ninetyTwoCL_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_ninetyTwoCL_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_ninetyTwoCL_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_ninetyTwoCL_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_ninetyTwoCL_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_ninetyTwoCL_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_ninetyTwoCL_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_ninetyTwoCL_3257 : Nat.Prime 3257 := by norm_num

private theorem prime_ninetyTwoCL_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_ninetyTwoCL_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_ninetyTwoCL_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_ninetyTwoCL_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_ninetyTwoCL_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_ninetyTwoCL_3929 : Nat.Prime 3929 := by norm_num

private theorem prime_ninetyTwoCL_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_ninetyTwoCL_4229 : Nat.Prime 4229 := by norm_num

private theorem prime_ninetyTwoCL_4259 : Nat.Prime 4259 := by norm_num

private theorem prime_ninetyTwoCL_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_ninetyTwoCL_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_ninetyTwoCL_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_ninetyTwoCL_4787 : Nat.Prime 4787 := by norm_num

private theorem prime_ninetyTwoCL_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_ninetyTwoCL_4943 : Nat.Prime 4943 := by norm_num

private theorem prime_ninetyTwoCL_5171 : Nat.Prime 5171 := by norm_num

private theorem prime_ninetyTwoCL_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_ninetyTwoCL_5237 : Nat.Prime 5237 := by norm_num

private theorem prime_ninetyTwoCL_5407 : Nat.Prime 5407 := by norm_num

private theorem prime_ninetyTwoCL_5483 : Nat.Prime 5483 := by norm_num

private theorem prime_ninetyTwoCL_5557 : Nat.Prime 5557 := by norm_num

private theorem prime_ninetyTwoCL_5591 : Nat.Prime 5591 := by norm_num

private theorem prime_ninetyTwoCL_5783 : Nat.Prime 5783 := by norm_num

private theorem prime_ninetyTwoCL_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_ninetyTwoCL_5849 : Nat.Prime 5849 := by norm_num

private theorem prime_ninetyTwoCL_5939 : Nat.Prime 5939 := by norm_num

private theorem prime_ninetyTwoCL_5981 : Nat.Prime 5981 := by norm_num

private theorem prime_ninetyTwoCL_6029 : Nat.Prime 6029 := by norm_num

private theorem prime_ninetyTwoCL_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_ninetyTwoCL_6113 : Nat.Prime 6113 := by norm_num

private theorem prime_ninetyTwoCL_6151 : Nat.Prime 6151 := by norm_num

private theorem prime_ninetyTwoCL_6211 : Nat.Prime 6211 := by norm_num

private theorem prime_ninetyTwoCL_6263 : Nat.Prime 6263 := by norm_num

private theorem prime_ninetyTwoCL_6271 : Nat.Prime 6271 := by norm_num

private theorem prime_ninetyTwoCL_6277 : Nat.Prime 6277 := by norm_num

private theorem prime_ninetyTwoCL_6661 : Nat.Prime 6661 := by norm_num

private theorem prime_ninetyTwoCL_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_ninetyTwoCL_7481 : Nat.Prime 7481 := by norm_num

private theorem prime_ninetyTwoCL_7703 : Nat.Prime 7703 := by norm_num

private theorem prime_ninetyTwoCL_7723 : Nat.Prime 7723 := by norm_num

private theorem prime_ninetyTwoCL_7873 : Nat.Prime 7873 := by norm_num

private theorem prime_ninetyTwoCL_8707 : Nat.Prime 8707 := by norm_num

private theorem prime_ninetyTwoCL_8783 : Nat.Prime 8783 := by norm_num

private theorem prime_ninetyTwoCL_8849 : Nat.Prime 8849 := by norm_num

private theorem prime_ninetyTwoCL_8887 : Nat.Prime 8887 := by norm_num

private theorem prime_ninetyTwoCL_9497 : Nat.Prime 9497 := by norm_num

private theorem prime_ninetyTwoCL_9623 : Nat.Prime 9623 := by norm_num

private theorem prime_ninetyTwoCL_9643 : Nat.Prime 9643 := by norm_num

private theorem prime_ninetyTwoCL_9719 : Nat.Prime 9719 := by norm_num

private theorem prime_ninetyTwoCL_9733 : Nat.Prime 9733 := by norm_num

private theorem prime_ninetyTwoCL_9901 : Nat.Prime 9901 := by norm_num

private theorem prime_ninetyTwoCL_10099 : Nat.Prime 10099 := by norm_num

private theorem prime_ninetyTwoCL_10223 : Nat.Prime 10223 := by norm_num

private theorem prime_ninetyTwoCL_10253 : Nat.Prime 10253 := by norm_num

private theorem prime_ninetyTwoCL_10331 : Nat.Prime 10331 := by norm_num

private theorem prime_ninetyTwoCL_10613 : Nat.Prime 10613 := by norm_num

private theorem prime_ninetyTwoCL_10889 : Nat.Prime 10889 := by norm_num

private theorem prime_ninetyTwoCL_11677 : Nat.Prime 11677 := by norm_num

private theorem prime_ninetyTwoCL_11903 : Nat.Prime 11903 := by norm_num

private theorem prime_ninetyTwoCL_12011 : Nat.Prime 12011 := by norm_num

private theorem prime_ninetyTwoCL_12037 : Nat.Prime 12037 := by norm_num

private theorem prime_ninetyTwoCL_12109 : Nat.Prime 12109 := by norm_num

private theorem prime_ninetyTwoCL_12227 : Nat.Prime 12227 := by norm_num

private theorem prime_ninetyTwoCL_12433 : Nat.Prime 12433 := by norm_num

private theorem prime_ninetyTwoCL_12763 : Nat.Prime 12763 := by norm_num

private theorem prime_ninetyTwoCL_13159 : Nat.Prime 13159 := by norm_num

private theorem prime_ninetyTwoCL_13259 : Nat.Prime 13259 := by norm_num

private theorem prime_ninetyTwoCL_13901 : Nat.Prime 13901 := by norm_num

private theorem prime_ninetyTwoCL_15131 : Nat.Prime 15131 := by norm_num

private theorem prime_ninetyTwoCL_15187 : Nat.Prime 15187 := by norm_num

private theorem prime_ninetyTwoCL_16361 : Nat.Prime 16361 := by norm_num

private theorem prime_ninetyTwoCL_16477 : Nat.Prime 16477 := by norm_num

private theorem prime_ninetyTwoCL_17911 : Nat.Prime 17911 := by norm_num

private theorem prime_ninetyTwoCL_18169 : Nat.Prime 18169 := by norm_num

private theorem prime_ninetyTwoCL_18229 : Nat.Prime 18229 := by norm_num

private theorem prime_ninetyTwoCL_18731 : Nat.Prime 18731 := by norm_num

private theorem prime_ninetyTwoCL_19139 : Nat.Prime 19139 := by norm_num

private theorem prime_ninetyTwoCL_19141 : Nat.Prime 19141 := by norm_num

private theorem prime_ninetyTwoCL_19157 : Nat.Prime 19157 := by norm_num

private theorem prime_ninetyTwoCL_19267 : Nat.Prime 19267 := by norm_num

private theorem prime_ninetyTwoCL_20047 : Nat.Prime 20047 := by norm_num

private theorem prime_ninetyTwoCL_20879 : Nat.Prime 20879 := by norm_num

private theorem prime_ninetyTwoCL_21017 : Nat.Prime 21017 := by norm_num

private theorem prime_ninetyTwoCL_22171 : Nat.Prime 22171 := by norm_num

private theorem prime_ninetyTwoCL_22571 : Nat.Prime 22571 := by norm_num

private theorem prime_ninetyTwoCL_24071 : Nat.Prime 24071 := by norm_num

private theorem prime_ninetyTwoCL_24709 : Nat.Prime 24709 := by norm_num

private theorem prime_ninetyTwoCL_25097 : Nat.Prime 25097 := by norm_num

private theorem prime_ninetyTwoCL_28549 : Nat.Prime 28549 := by norm_num

private theorem prime_ninetyTwoCL_30187 : Nat.Prime 30187 := by norm_num

private theorem prime_ninetyTwoCL_30271 : Nat.Prime 30271 := by norm_num

private theorem prime_ninetyTwoCL_30293 : Nat.Prime 30293 := by norm_num

private theorem prime_ninetyTwoCL_31231 : Nat.Prime 31231 := by norm_num

private theorem prime_ninetyTwoCL_32363 : Nat.Prime 32363 := by norm_num

private theorem prime_ninetyTwoCL_33811 : Nat.Prime 33811 := by norm_num

private theorem prime_ninetyTwoCL_34519 : Nat.Prime 34519 := by norm_num

private theorem prime_ninetyTwoCL_35339 : Nat.Prime 35339 := by norm_num

private theorem prime_ninetyTwoCL_35531 : Nat.Prime 35531 := by norm_num

private theorem prime_ninetyTwoCL_35603 : Nat.Prime 35603 := by norm_num

private theorem prime_ninetyTwoCL_36877 : Nat.Prime 36877 := by norm_num

private theorem prime_ninetyTwoCL_38333 : Nat.Prime 38333 := by norm_num

private theorem prime_ninetyTwoCL_40099 : Nat.Prime 40099 := by norm_num

private theorem prime_ninetyTwoCL_42139 : Nat.Prime 42139 := by norm_num

private theorem prime_ninetyTwoCL_42589 : Nat.Prime 42589 := by norm_num

private theorem prime_ninetyTwoCL_43649 : Nat.Prime 43649 := by norm_num

private theorem prime_ninetyTwoCL_47189 : Nat.Prime 47189 := by norm_num

private theorem prime_ninetyTwoCL_47389 : Nat.Prime 47389 := by norm_num

private theorem prime_ninetyTwoCL_50329 : Nat.Prime 50329 := by norm_num

private theorem prime_ninetyTwoCL_54377 : Nat.Prime 54377 := by norm_num

private theorem prime_ninetyTwoCL_54679 : Nat.Prime 54679 := by norm_num

private theorem prime_ninetyTwoCL_55219 : Nat.Prime 55219 := by norm_num

private theorem prime_ninetyTwoCL_56701 : Nat.Prime 56701 := by norm_num

private theorem prime_ninetyTwoCL_57847 : Nat.Prime 57847 := by norm_num

private theorem prime_ninetyTwoCL_59273 : Nat.Prime 59273 := by norm_num

private theorem prime_ninetyTwoCL_62327 : Nat.Prime 62327 := by norm_num

private theorem prime_ninetyTwoCL_66683 : Nat.Prime 66683 := by norm_num

private theorem prime_ninetyTwoCL_71161 : Nat.Prime 71161 := by norm_num

private theorem prime_ninetyTwoCL_80263 : Nat.Prime 80263 := by norm_num

private theorem prime_ninetyTwoCL_81019 : Nat.Prime 81019 := by norm_num

private theorem prime_ninetyTwoCL_82051 : Nat.Prime 82051 := by norm_num

private theorem prime_ninetyTwoCL_82301 : Nat.Prime 82301 := by norm_num

private theorem prime_ninetyTwoCL_83089 : Nat.Prime 83089 := by norm_num

private theorem prime_ninetyTwoCL_87323 : Nat.Prime 87323 := by norm_num

private theorem prime_ninetyTwoCL_89611 : Nat.Prime 89611 := by norm_num

private theorem prime_ninetyTwoCL_89689 : Nat.Prime 89689 := by norm_num

private theorem prime_ninetyTwoCL_92821 : Nat.Prime 92821 := by norm_num

private theorem prime_ninetyTwoCL_104717 : Nat.Prime 104717 := by norm_num

private theorem prime_ninetyTwoCL_105277 : Nat.Prime 105277 := by norm_num

private theorem prime_ninetyTwoCL_108799 : Nat.Prime 108799 := by norm_num

private theorem prime_ninetyTwoCL_110039 : Nat.Prime 110039 := by norm_num

private theorem prime_ninetyTwoCL_117413 : Nat.Prime 117413 := by norm_num

private theorem prime_ninetyTwoCL_122819 : Nat.Prime 122819 := by norm_num

private theorem prime_ninetyTwoCL_126601 : Nat.Prime 126601 := by norm_num

private theorem prime_ninetyTwoCL_127363 : Nat.Prime 127363 := by norm_num

private theorem prime_ninetyTwoCL_127979 : Nat.Prime 127979 := by norm_num

private theorem prime_ninetyTwoCL_130969 : Nat.Prime 130969 := by norm_num

private theorem prime_ninetyTwoCL_131899 : Nat.Prime 131899 := by norm_num

private theorem prime_ninetyTwoCL_142157 : Nat.Prime 142157 := by norm_num

private theorem prime_ninetyTwoCL_143483 : Nat.Prime 143483 := by norm_num

private theorem prime_ninetyTwoCL_145193 : Nat.Prime 145193 := by norm_num

private theorem prime_ninetyTwoCL_151007 : Nat.Prime 151007 := by norm_num

private theorem prime_ninetyTwoCL_152077 : Nat.Prime 152077 := by norm_num

private theorem prime_ninetyTwoCL_153319 : Nat.Prime 153319 := by norm_num

private theorem prime_ninetyTwoCL_158429 : Nat.Prime 158429 := by norm_num

private theorem prime_ninetyTwoCL_159673 : Nat.Prime 159673 := by norm_num

private theorem prime_ninetyTwoCL_160453 : Nat.Prime 160453 := by norm_num

private theorem prime_ninetyTwoCL_174901 : Nat.Prime 174901 := by norm_num

private theorem prime_ninetyTwoCL_179819 : Nat.Prime 179819 := by norm_num

private theorem prime_ninetyTwoCL_196073 : Nat.Prime 196073 := by norm_num

private theorem prime_ninetyTwoCL_198929 : Nat.Prime 198929 := by norm_num

private theorem prime_ninetyTwoCL_219277 : Nat.Prime 219277 := by norm_num

private theorem prime_ninetyTwoCL_229399 : Nat.Prime 229399 := by norm_num

private theorem prime_ninetyTwoCL_229759 : Nat.Prime 229759 := by norm_num

private theorem prime_ninetyTwoCL_253247 : Nat.Prime 253247 := by norm_num

private theorem prime_ninetyTwoCL_259907 : Nat.Prime 259907 := by norm_num

private theorem prime_ninetyTwoCL_261407 : Nat.Prime 261407 := by norm_num

private theorem prime_ninetyTwoCL_266681 : Nat.Prime 266681 := by norm_num

private theorem prime_ninetyTwoCL_277483 : Nat.Prime 277483 := by norm_num

private theorem prime_ninetyTwoCL_289847 : Nat.Prime 289847 := by norm_num

private theorem prime_ninetyTwoCL_297589 : Nat.Prime 297589 := by norm_num

private theorem prime_ninetyTwoCL_298427 : Nat.Prime 298427 := by norm_num

private theorem prime_ninetyTwoCL_303491 : Nat.Prime 303491 := by norm_num

private theorem prime_ninetyTwoCL_305017 : Nat.Prime 305017 := by norm_num

private theorem prime_ninetyTwoCL_308093 : Nat.Prime 308093 := by norm_num

private theorem prime_ninetyTwoCL_335207 : Nat.Prime 335207 := by norm_num

private theorem prime_ninetyTwoCL_337537 : Nat.Prime 337537 := by norm_num

private theorem prime_ninetyTwoCL_342847 : Nat.Prime 342847 := by norm_num

private theorem prime_ninetyTwoCL_347063 : Nat.Prime 347063 := by norm_num

private theorem prime_ninetyTwoCL_352381 : Nat.Prime 352381 := by norm_num

private theorem prime_ninetyTwoCL_354169 : Nat.Prime 354169 := by norm_num

private theorem prime_ninetyTwoCL_361357 : Nat.Prime 361357 := by norm_num

private theorem prime_ninetyTwoCL_365569 : Nat.Prime 365569 := by norm_num

private theorem prime_ninetyTwoCL_379417 : Nat.Prime 379417 := by norm_num

private theorem prime_ninetyTwoCL_380879 : Nat.Prime 380879 := by norm_num

private theorem prime_ninetyTwoCL_383611 : Nat.Prime 383611 := by norm_num

private theorem prime_ninetyTwoCL_398129 : Nat.Prime 398129 := by norm_num

private theorem prime_ninetyTwoCL_402613 : Nat.Prime 402613 := by norm_num

private theorem prime_ninetyTwoCL_411197 : Nat.Prime 411197 := by norm_num

private theorem prime_ninetyTwoCL_417133 : Nat.Prime 417133 := by norm_num

private theorem prime_ninetyTwoCL_421049 : Nat.Prime 421049 := by norm_num

private theorem prime_ninetyTwoCL_439903 : Nat.Prime 439903 := by norm_num

private theorem prime_ninetyTwoCL_460079 : Nat.Prime 460079 := by norm_num

private theorem prime_ninetyTwoCL_479317 : Nat.Prime 479317 := by norm_num

private theorem prime_ninetyTwoCL_496681 : Nat.Prime 496681 := by norm_num

private theorem prime_ninetyTwoCL_499321 : Nat.Prime 499321 := by norm_num

private theorem prime_ninetyTwoCL_525809 : Nat.Prime 525809 := by norm_num

private theorem prime_ninetyTwoCL_533321 : Nat.Prime 533321 := by norm_num

private theorem prime_ninetyTwoCL_537307 : Nat.Prime 537307 := by norm_num

private theorem prime_ninetyTwoCL_573329 : Nat.Prime 573329 := by norm_num

private theorem prime_ninetyTwoCL_605257 : Nat.Prime 605257 := by norm_num

private theorem prime_ninetyTwoCL_615427 : Nat.Prime 615427 := by norm_num

private theorem prime_ninetyTwoCL_627667 : Nat.Prime 627667 := by norm_num

private theorem prime_ninetyTwoCL_631559 : Nat.Prime 631559 := by norm_num

private theorem prime_ninetyTwoCL_676373 : Nat.Prime 676373 := by norm_num

private theorem prime_ninetyTwoCL_734233 : Nat.Prime 734233 := by norm_num

private theorem prime_ninetyTwoCL_771283 : Nat.Prime 771283 := by norm_num

private theorem prime_ninetyTwoCL_780499 : Nat.Prime 780499 := by norm_num

private theorem prime_ninetyTwoCL_794153 : Nat.Prime 794153 := by norm_num

private theorem prime_ninetyTwoCL_804697 : Nat.Prime 804697 := by norm_num

private theorem prime_ninetyTwoCL_833923 : Nat.Prime 833923 := by norm_num

private theorem prime_ninetyTwoCL_861719 : Nat.Prime 861719 := by norm_num

private theorem prime_ninetyTwoCL_863123 : Nat.Prime 863123 := by norm_num

private theorem prime_ninetyTwoCL_920863 : Nat.Prime 920863 := by norm_num

private theorem prime_ninetyTwoCL_932447 : Nat.Prime 932447 := by norm_num

private theorem prime_ninetyTwoCL_998737 : Nat.Prime 998737 := by norm_num

private theorem prime_ninetyTwoCL_1001069 : Nat.Prime 1001069 := by norm_num

private theorem prime_ninetyTwoCL_1005551 : Nat.Prime 1005551 := by norm_num

private theorem prime_ninetyTwoCL_1038797 : Nat.Prime 1038797 := by norm_num

private theorem prime_ninetyTwoCL_1059889 : Nat.Prime 1059889 := by norm_num

private theorem prime_ninetyTwoCL_1104139 : Nat.Prime 1104139 := by norm_num

private theorem prime_ninetyTwoCL_1151593 : Nat.Prime 1151593 := by norm_num

private theorem prime_ninetyTwoCL_1179677 : Nat.Prime 1179677 := by norm_num

private theorem prime_ninetyTwoCL_1184143 : Nat.Prime 1184143 := by norm_num

private theorem prime_ninetyTwoCL_1209707 : Nat.Prime 1209707 := by norm_num

private theorem prime_ninetyTwoCL_1224029 : Nat.Prime 1224029 := by norm_num

private theorem prime_ninetyTwoCL_1327091 : Nat.Prime 1327091 := by norm_num

private theorem prime_ninetyTwoCL_1353613 : Nat.Prime 1353613 := by norm_num

private theorem prime_ninetyTwoCL_1441127 : Nat.Prime 1441127 := by norm_num

private theorem prime_ninetyTwoCL_1503989 : Nat.Prime 1503989 := by norm_num

private theorem prime_ninetyTwoCL_1550771 : Nat.Prime 1550771 := by norm_num

private theorem prime_ninetyTwoCL_1696973 : Nat.Prime 1696973 := by norm_num

private theorem prime_ninetyTwoCL_1754681 : Nat.Prime 1754681 := by norm_num

private theorem prime_ninetyTwoCL_1819931 : Nat.Prime 1819931 := by norm_num

private theorem prime_ninetyTwoCL_1927031 : Nat.Prime 1927031 := by norm_num

private theorem prime_ninetyTwoCL_2024227 : Nat.Prime 2024227 := by norm_num

private theorem prime_ninetyTwoCL_2034257 : Nat.Prime 2034257 := by norm_num

private theorem prime_ninetyTwoCL_2037689 : Nat.Prime 2037689 := by norm_num

private theorem prime_ninetyTwoCL_2071591 : Nat.Prime 2071591 := by norm_num

private theorem prime_ninetyTwoCL_2154791 : Nat.Prime 2154791 := by norm_num

private theorem prime_ninetyTwoCL_2238259 : Nat.Prime 2238259 := by norm_num

private theorem prime_ninetyTwoCL_2331191 : Nat.Prime 2331191 := by norm_num

private theorem prime_ninetyTwoCL_2723863 : Nat.Prime 2723863 := by norm_num

private theorem prime_ninetyTwoCL_2788939 : Nat.Prime 2788939 := by norm_num

private theorem prime_ninetyTwoCL_2813693 : Nat.Prime 2813693 := by norm_num

private theorem prime_ninetyTwoCL_2944547 : Nat.Prime 2944547 := by norm_num

private theorem prime_ninetyTwoCL_3596003 : Nat.Prime 3596003 := by norm_num

private theorem prime_ninetyTwoCL_3823103 : Nat.Prime 3823103 := by norm_num

private theorem prime_ninetyTwoCL_3949069 : Nat.Prime 3949069 := by norm_num

private theorem prime_ninetyTwoCL_4080409 : Nat.Prime 4080409 := by norm_num

private theorem prime_ninetyTwoCL_4630603 : Nat.Prime 4630603 := by norm_num

private theorem prime_ninetyTwoCL_4878217 : Nat.Prime 4878217 := by norm_num

private theorem prime_ninetyTwoCL_5132837 : Nat.Prime 5132837 := by norm_num

private theorem prime_ninetyTwoCL_5567183 : Nat.Prime 5567183 := by norm_num

private theorem prime_ninetyTwoCL_5887711 : Nat.Prime 5887711 := by norm_num

private theorem prime_ninetyTwoCL_6227737 : Nat.Prime 6227737 := by norm_num

private theorem prime_ninetyTwoCL_6256819 : Nat.Prime 6256819 := by norm_num

private theorem prime_ninetyTwoCL_6295103 : Nat.Prime 6295103 := by norm_num

private theorem prime_ninetyTwoCL_6295283 : Nat.Prime 6295283 := by norm_num

private theorem prime_ninetyTwoCL_7094471 : Nat.Prime 7094471 := by norm_num

private theorem prime_ninetyTwoCL_7185247 : Nat.Prime 7185247 := by norm_num

private theorem prime_ninetyTwoCL_7188047 : Nat.Prime 7188047 := by norm_num

private theorem prime_ninetyTwoCL_7232503 : Nat.Prime 7232503 := by norm_num

private theorem prime_ninetyTwoCL_7626097 : Nat.Prime 7626097 := by norm_num

private theorem prime_ninetyTwoCL_7744057 : Nat.Prime 7744057 := by norm_num

private theorem prime_ninetyTwoCL_8632123 : Nat.Prime 8632123 := by norm_num

private theorem prime_ninetyTwoCL_9210791 : Nat.Prime 9210791 := by norm_num

private theorem prime_ninetyTwoCL_9807503 : Nat.Prime 9807503 := by norm_num

private theorem prime_ninetyTwoCL_10219333 : Nat.Prime 10219333 := by norm_num

private theorem prime_ninetyTwoCL_10356169 : Nat.Prime 10356169 := by norm_num

private theorem prime_ninetyTwoCL_11740067 : Nat.Prime 11740067 := by norm_num

private theorem prime_ninetyTwoCL_13481711 : Nat.Prime 13481711 := by norm_num

private theorem prime_ninetyTwoCL_14467181 : Nat.Prime 14467181 := by norm_num

private theorem prime_ninetyTwoCL_14484727 : Nat.Prime 14484727 := by norm_num

private theorem prime_ninetyTwoCL_16258933 : Nat.Prime 16258933 := by norm_num

private theorem prime_ninetyTwoCL_16720967 : Nat.Prime 16720967 := by norm_num

private theorem prime_ninetyTwoCL_18717199 : Nat.Prime 18717199 := by norm_num

private theorem prime_ninetyTwoCL_19088759 : Nat.Prime 19088759 := by norm_num

private theorem prime_ninetyTwoCL_22617983 : Nat.Prime 22617983 := by norm_num

private theorem prime_ninetyTwoCL_24072331 : Nat.Prime 24072331 := by norm_num

private theorem prime_ninetyTwoCL_24584561 : Nat.Prime 24584561 := by norm_num

private theorem prime_ninetyTwoCL_25533679 : Nat.Prime 25533679 := by norm_num

private theorem prime_ninetyTwoCL_25540913 : Nat.Prime 25540913 := by norm_num

private theorem prime_ninetyTwoCL_26694839 : Nat.Prime 26694839 := by norm_num

private theorem prime_ninetyTwoCL_26834567 : Nat.Prime 26834567 := by norm_num

private theorem prime_ninetyTwoCL_28448689 : Nat.Prime 28448689 := by norm_num

private theorem prime_ninetyTwoCL_28519531 : Nat.Prime 28519531 := by norm_num

private theorem prime_ninetyTwoCL_28601297 : Nat.Prime 28601297 := by norm_num

private theorem prime_ninetyTwoCL_31067737 : Nat.Prime 31067737 := by
  apply lucas_primality 31067737 (5 : ZMod 31067737)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19, 1), (9733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19, 1), (9733, 1)] : List FactorBlock).map factorBlockValue).prod) = 31067737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_9733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31067737) ^ 15533868 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 31067737) ^ 10355912 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 31067737) ^ 4438248 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 31067737) ^ 1635144 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 31067737) ^ 3192 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_35462263 : Nat.Prime 35462263 := by
  apply lucas_primality 35462263 (3 : ZMod 35462263)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (537307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (537307, 1)] : List FactorBlock).map factorBlockValue).prod) = 35462263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_537307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35462263) ^ 17731131 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 35462263) ^ 11820754 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 35462263) ^ 3223842 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 35462263) ^ 66 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_35901407 : Nat.Prime 35901407 := by
  apply lucas_primality 35901407 (5 : ZMod 35901407)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (593, 1), (30271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (593, 1), (30271, 1)] : List FactorBlock).map factorBlockValue).prod) = 35901407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_593
      · exact prime_ninetyTwoCL_30271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35901407) ^ 17950703 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 35901407) ^ 60542 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 35901407) ^ 1186 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_36165971 : Nat.Prime 36165971 := by
  apply lucas_primality 36165971 (2 : ZMod 36165971)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (229, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (229, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) = 36165971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_229
      · exact prime_ninetyTwoCL_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36165971) ^ 18082985 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36165971) ^ 7233194 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36165971) ^ 2127410 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36165971) ^ 157930 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36165971) ^ 38930 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_37770619 : Nat.Prime 37770619 := by
  apply lucas_primality 37770619 (2 : ZMod 37770619)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6295103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6295103, 1)] : List FactorBlock).map factorBlockValue).prod) = 37770619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_6295103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37770619) ^ 18885309 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 37770619) ^ 12590206 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 37770619) ^ 6 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_38360459 : Nat.Prime 38360459 := by
  apply lucas_primality 38360459 (2 : ZMod 38360459)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (833923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (833923, 1)] : List FactorBlock).map factorBlockValue).prod) = 38360459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_833923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38360459) ^ 19180229 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 38360459) ^ 1667846 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 38360459) ^ 46 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_40260863 : Nat.Prime 40260863 := by
  apply lucas_primality 40260863 (5 : ZMod 40260863)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1184143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1184143, 1)] : List FactorBlock).map factorBlockValue).prod) = 40260863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_1184143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40260863) ^ 20130431 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 40260863) ^ 2368286 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 40260863) ^ 34 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_41041811 : Nat.Prime 41041811 := by
  apply lucas_primality 41041811 (2 : ZMod 41041811)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (87323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (87323, 1)] : List FactorBlock).map factorBlockValue).prod) = 41041811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_47
      · exact prime_ninetyTwoCL_87323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41041811) ^ 20520905 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41041811) ^ 8208362 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41041811) ^ 873230 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41041811) ^ 470 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_43282951 : Nat.Prime 43282951 := by
  apply lucas_primality 43282951 (6 : ZMod 43282951)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (19, 1), (15187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (19, 1), (15187, 1)] : List FactorBlock).map factorBlockValue).prod) = 43282951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_15187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 43282951) ^ 21641475 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 43282951) ^ 14427650 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 43282951) ^ 8656590 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 43282951) ^ 2278050 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 43282951) ^ 2850 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_51792739 : Nat.Prime 51792739 := by
  apply lucas_primality 51792739 (3 : ZMod 51792739)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8632123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8632123, 1)] : List FactorBlock).map factorBlockValue).prod) = 51792739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_8632123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 51792739) ^ 25896369 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 51792739) ^ 17264246 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 51792739) ^ 6 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_52976207 : Nat.Prime 52976207 := by
  apply lucas_primality 52976207 (5 : ZMod 52976207)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (691, 1), (38333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (691, 1), (38333, 1)] : List FactorBlock).map factorBlockValue).prod) = 52976207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_691
      · exact prime_ninetyTwoCL_38333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52976207) ^ 26488103 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 52976207) ^ 76666 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 52976207) ^ 1382 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_54032009 : Nat.Prime 54032009 := by
  apply lucas_primality 54032009 (3 : ZMod 54032009)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (223, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (223, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 54032009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_31
      · exact prime_ninetyTwoCL_223
      · exact prime_ninetyTwoCL_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54032009) ^ 27016004 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 54032009) ^ 1742968 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 54032009) ^ 242296 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 54032009) ^ 55304 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_54810443 : Nat.Prime 54810443 := by
  apply lucas_primality 54810443 (2 : ZMod 54810443)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5233, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5233, 1), (5237, 1)] : List FactorBlock).map factorBlockValue).prod) = 54810443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5233
      · exact prime_ninetyTwoCL_5237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54810443) ^ 27405221 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54810443) ^ 10474 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54810443) ^ 10466 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_59724209 : Nat.Prime 59724209 := by
  apply lucas_primality 59724209 (3 : ZMod 59724209)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (181, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (181, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 59724209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_181
      · exact prime_ninetyTwoCL_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59724209) ^ 29862104 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 59724209) ^ 1456688 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 59724209) ^ 329968 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 59724209) ^ 118736 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_60333061 : Nat.Prime 60333061 := by
  apply lucas_primality 60333061 (6 : ZMod 60333061)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1005551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1005551, 1)] : List FactorBlock).map factorBlockValue).prod) = 60333061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_1005551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 60333061) ^ 30166530 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 60333061) ^ 20111020 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 60333061) ^ 12066612 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 60333061) ^ 60 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_60726811 : Nat.Prime 60726811 := by
  apply lucas_primality 60726811 (2 : ZMod 60726811)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2024227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2024227, 1)] : List FactorBlock).map factorBlockValue).prod) = 60726811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_2024227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60726811) ^ 30363405 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 60726811) ^ 20242270 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 60726811) ^ 12145362 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 60726811) ^ 30 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_62266199 : Nat.Prime 62266199 := by
  apply lucas_primality 62266199 (7 : ZMod 62266199)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1353613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1353613, 1)] : List FactorBlock).map factorBlockValue).prod) = 62266199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_1353613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 62266199) ^ 31133099 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 62266199) ^ 2707226 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 62266199) ^ 46 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_63409589 : Nat.Prime 63409589 := by
  apply lucas_primality 63409589 (2 : ZMod 63409589)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1441127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1441127, 1)] : List FactorBlock).map factorBlockValue).prod) = 63409589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_1441127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63409589) ^ 31704794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 63409589) ^ 5764508 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 63409589) ^ 44 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_66353663 : Nat.Prime 66353663 := by
  apply lucas_primality 66353663 (5 : ZMod 66353663)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (42589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (42589, 1)] : List FactorBlock).map factorBlockValue).prod) = 66353663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_42589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66353663) ^ 33176831 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 66353663) ^ 3492298 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 66353663) ^ 1618382 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 66353663) ^ 1558 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_68130497 : Nat.Prime 68130497 := by
  apply lucas_primality 68130497 (3 : ZMod 68130497)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (152077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (152077, 1)] : List FactorBlock).map factorBlockValue).prod) = 68130497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_152077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68130497) ^ 34065248 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 68130497) ^ 9732928 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 68130497) ^ 448 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_71272867 : Nat.Prime 71272867 := by
  apply lucas_primality 71272867 (2 : ZMod 71272867)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1696973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1696973, 1)] : List FactorBlock).map factorBlockValue).prod) = 71272867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_1696973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71272867) ^ 35636433 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 71272867) ^ 23757622 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 71272867) ^ 10181838 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 71272867) ^ 42 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_76260971 : Nat.Prime 76260971 := by
  apply lucas_primality 76260971 (6 : ZMod 76260971)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7626097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7626097, 1)] : List FactorBlock).map factorBlockValue).prod) = 76260971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7626097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 76260971) ^ 38130485 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 76260971) ^ 15252194 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 76260971) ^ 10 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_79732171 : Nat.Prime 79732171 := by
  apply lucas_primality 79732171 (3 : ZMod 79732171)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (6661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (6661, 1)] : List FactorBlock).map factorBlockValue).prod) = 79732171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_6661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 79732171) ^ 39866085 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 79732171) ^ 26577390 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 79732171) ^ 15946434 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 79732171) ^ 11390310 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 79732171) ^ 4196430 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 79732171) ^ 11970 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_90804821 : Nat.Prime 90804821 := by
  apply lucas_primality 90804821 (2 : ZMod 90804821)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (43, 1), (6211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (43, 1), (6211, 1)] : List FactorBlock).map factorBlockValue).prod) = 90804821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_43
      · exact prime_ninetyTwoCL_6211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90804821) ^ 45402410 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 90804821) ^ 18160964 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 90804821) ^ 5341460 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 90804821) ^ 2111740 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 90804821) ^ 14620 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_96823717 : Nat.Prime 96823717 := by
  apply lucas_primality 96823717 (2 : ZMod 96823717)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (66683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (66683, 1)] : List FactorBlock).map factorBlockValue).prod) = 96823717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_66683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96823717) ^ 48411858 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 96823717) ^ 32274572 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 96823717) ^ 8802156 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 96823717) ^ 1452 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_97860083 : Nat.Prime 97860083 := by
  apply lucas_primality 97860083 (2 : ZMod 97860083)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (337, 1), (145193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (337, 1), (145193, 1)] : List FactorBlock).map factorBlockValue).prod) = 97860083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_337
      · exact prime_ninetyTwoCL_145193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 97860083) ^ 48930041 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 97860083) ^ 290386 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 97860083) ^ 674 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_97866917 : Nat.Prime 97866917 := by
  apply lucas_primality 97866917 (3 : ZMod 97866917)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (499321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (499321, 1)] : List FactorBlock).map factorBlockValue).prod) = 97866917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_499321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 97866917) ^ 48933458 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 97866917) ^ 13980988 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 97866917) ^ 196 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_98262137 : Nat.Prime 98262137 := by
  apply lucas_primality 98262137 (3 : ZMod 98262137)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1754681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1754681, 1)] : List FactorBlock).map factorBlockValue).prod) = 98262137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_1754681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98262137) ^ 49131068 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 98262137) ^ 14037448 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 98262137) ^ 56 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_112391857 : Nat.Prime 112391857 := by
  apply lucas_primality 112391857 (5 : ZMod 112391857)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (780499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (780499, 1)] : List FactorBlock).map factorBlockValue).prod) = 112391857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_780499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 112391857) ^ 56195928 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 112391857) ^ 37463952 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 112391857) ^ 144 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_132671047 : Nat.Prime 132671047 := by
  apply lucas_primality 132671047 (6 : ZMod 132671047)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1103, 1), (20047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1103, 1), (20047, 1)] : List FactorBlock).map factorBlockValue).prod) = 132671047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_1103
      · exact prime_ninetyTwoCL_20047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 132671047) ^ 66335523 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 132671047) ^ 44223682 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 132671047) ^ 120282 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 132671047) ^ 6618 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_137756257 : Nat.Prime 137756257 := by
  apply lucas_primality 137756257 (10 : ZMod 137756257)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (73, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (73, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) = 137756257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_73
      · exact prime_ninetyTwoCL_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 137756257) ^ 68878128 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 137756257) ^ 45918752 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 137756257) ^ 12523296 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 137756257) ^ 1887072 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 137756257) ^ 77088 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_144552833 : Nat.Prime 144552833 := by
  apply lucas_primality 144552833 (3 : ZMod 144552833)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (59, 1), (19141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (59, 1), (19141, 1)] : List FactorBlock).map factorBlockValue).prod) = 144552833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_59
      · exact prime_ninetyTwoCL_19141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 144552833) ^ 72276416 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 144552833) ^ 2450048 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 144552833) ^ 7552 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_148994723 : Nat.Prime 148994723 := by
  apply lucas_primality 148994723 (2 : ZMod 148994723)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (257, 1), (3257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (257, 1), (3257, 1)] : List FactorBlock).map factorBlockValue).prod) = 148994723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_89
      · exact prime_ninetyTwoCL_257
      · exact prime_ninetyTwoCL_3257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 148994723) ^ 74497361 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 148994723) ^ 1674098 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 148994723) ^ 579746 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 148994723) ^ 45746 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_167063401 : Nat.Prime 167063401 := by
  apply lucas_primality 167063401 (13 : ZMod 167063401)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (7, 1), (13259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (7, 1), (13259, 1)] : List FactorBlock).map factorBlockValue).prod) = 167063401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_13259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 167063401) ^ 83531700 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 167063401) ^ 55687800 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 167063401) ^ 33412680 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 167063401) ^ 23866200 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 167063401) ^ 12600 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_170666081 : Nat.Prime 170666081 := by
  apply lucas_primality 170666081 (3 : ZMod 170666081)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (82051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (82051, 1)] : List FactorBlock).map factorBlockValue).prod) = 170666081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_82051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 170666081) ^ 85333040 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 170666081) ^ 34133216 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 170666081) ^ 13128160 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 170666081) ^ 2080 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_189108973 : Nat.Prime 189108973 := by
  apply lucas_primality 189108973 (5 : ZMod 189108973)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 3), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 3), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 189108973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 189108973) ^ 94554486 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 189108973) ^ 63036324 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 189108973) ^ 14546844 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 189108973) ^ 237276 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_206702101 : Nat.Prime 206702101 := by
  apply lucas_primality 206702101 (6 : ZMod 206702101)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (11, 1), (20879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (11, 1), (20879, 1)] : List FactorBlock).map factorBlockValue).prod) = 206702101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_20879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 206702101) ^ 103351050 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 206702101) ^ 68900700 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 206702101) ^ 41340420 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 206702101) ^ 18791100 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 206702101) ^ 9900 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_211793063 : Nat.Prime 211793063 := by
  apply lucas_primality 211793063 (5 : ZMod 211793063)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (354169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (354169, 1)] : List FactorBlock).map factorBlockValue).prod) = 211793063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_354169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 211793063) ^ 105896531 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 211793063) ^ 16291774 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 211793063) ^ 9208394 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 211793063) ^ 598 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_237996971 : Nat.Prime 237996971 := by
  apply lucas_primality 237996971 (2 : ZMod 237996971)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (335207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (335207, 1)] : List FactorBlock).map factorBlockValue).prod) = 237996971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_71
      · exact prime_ninetyTwoCL_335207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237996971) ^ 118998485 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 237996971) ^ 47599394 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 237996971) ^ 3352070 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 237996971) ^ 710 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_246586877 : Nat.Prime 246586877 := by
  apply lucas_primality 246586877 (2 : ZMod 246586877)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3221, 1), (19139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3221, 1), (19139, 1)] : List FactorBlock).map factorBlockValue).prod) = 246586877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3221
      · exact prime_ninetyTwoCL_19139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 246586877) ^ 123293438 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 246586877) ^ 76556 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 246586877) ^ 12884 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_345692089 : Nat.Prime 345692089 := by
  apply lucas_primality 345692089 (11 : ZMod 345692089)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (631, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (631, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 345692089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_631
      · exact prime_ninetyTwoCL_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 345692089) ^ 172846044 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 345692089) ^ 115230696 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 345692089) ^ 49384584 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 345692089) ^ 547848 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 345692089) ^ 318024 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_451196701 : Nat.Prime 451196701 := by
  apply lucas_primality 451196701 (6 : ZMod 451196701)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (1503989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (1503989, 1)] : List FactorBlock).map factorBlockValue).prod) = 451196701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_1503989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 451196701) ^ 225598350 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 451196701) ^ 150398900 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 451196701) ^ 90239340 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 451196701) ^ 300 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_453910609 : Nat.Prime 453910609 := by
  apply lucas_primality 453910609 (7 : ZMod 453910609)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (17, 1), (19, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (17, 1), (19, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 453910609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 453910609) ^ 226955304 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 453910609) ^ 151303536 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 453910609) ^ 26700624 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 453910609) ^ 23890032 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 453910609) ^ 139536 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_456312497 : Nat.Prime 456312497 := by
  apply lucas_primality 456312497 (3 : ZMod 456312497)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (28519531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (28519531, 1)] : List FactorBlock).map factorBlockValue).prod) = 456312497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_28519531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 456312497) ^ 228156248 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 456312497) ^ 16 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_462830947 : Nat.Prime 462830947 := by
  apply lucas_primality 462830947 (2 : ZMod 462830947)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (709, 1), (108799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (709, 1), (108799, 1)] : List FactorBlock).map factorBlockValue).prod) = 462830947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_709
      · exact prime_ninetyTwoCL_108799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 462830947) ^ 231415473 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 462830947) ^ 154276982 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 462830947) ^ 652794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 462830947) ^ 4254 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_475214653 : Nat.Prime 475214653 := by
  apply lucas_primality 475214653 (5 : ZMod 475214653)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (67, 1), (17911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (67, 1), (17911, 1)] : List FactorBlock).map factorBlockValue).prod) = 475214653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_67
      · exact prime_ninetyTwoCL_17911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 475214653) ^ 237607326 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 475214653) ^ 158404884 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 475214653) ^ 43201332 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 475214653) ^ 7092756 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 475214653) ^ 26532 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_590965097 : Nat.Prime 590965097 := by
  apply lucas_primality 590965097 (3 : ZMod 590965097)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (277, 1), (266681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (277, 1), (266681, 1)] : List FactorBlock).map factorBlockValue).prod) = 590965097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_277
      · exact prime_ninetyTwoCL_266681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 590965097) ^ 295482548 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 590965097) ^ 2133448 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 590965097) ^ 2216 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_634658863 : Nat.Prime 634658863 := by
  apply lucas_primality 634658863 (3 : ZMod 634658863)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (5567183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (5567183, 1)] : List FactorBlock).map factorBlockValue).prod) = 634658863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_5567183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 634658863) ^ 317329431 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 634658863) ^ 211552954 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 634658863) ^ 33403098 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 634658863) ^ 114 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_636975851 : Nat.Prime 636975851 := by
  apply lucas_primality 636975851 (2 : ZMod 636975851)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1819931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1819931, 1)] : List FactorBlock).map factorBlockValue).prod) = 636975851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_1819931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 636975851) ^ 318487925 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 636975851) ^ 127395170 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 636975851) ^ 90996550 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 636975851) ^ 350 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_661825331 : Nat.Prime 661825331 := by
  apply lucas_primality 661825331 (2 : ZMod 661825331)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (67, 1), (21017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (67, 1), (21017, 1)] : List FactorBlock).map factorBlockValue).prod) = 661825331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_47
      · exact prime_ninetyTwoCL_67
      · exact prime_ninetyTwoCL_21017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 661825331) ^ 330912665 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 661825331) ^ 132365066 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 661825331) ^ 14081390 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 661825331) ^ 9877990 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 661825331) ^ 31490 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_786097097 : Nat.Prime 786097097 := by
  apply lucas_primality 786097097 (3 : ZMod 786097097)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (98262137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (98262137, 1)] : List FactorBlock).map factorBlockValue).prod) = 786097097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_98262137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 786097097) ^ 393048548 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 786097097) ^ 8 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1053518303 : Nat.Prime 1053518303 := by
  apply lucas_primality 1053518303 (5 : ZMod 1053518303)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8887, 1), (59273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8887, 1), (59273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1053518303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_8887
      · exact prime_ninetyTwoCL_59273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1053518303) ^ 526759151 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1053518303) ^ 118546 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1053518303) ^ 17774 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1127679283 : Nat.Prime 1127679283 := by
  apply lucas_primality 1127679283 (3 : ZMod 1127679283)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (2723863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (2723863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1127679283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_2723863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1127679283) ^ 563839641 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1127679283) ^ 375893094 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1127679283) ^ 49029534 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1127679283) ^ 414 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1129808707 : Nat.Prime 1129808707 := by
  apply lucas_primality 1129808707 (5 : ZMod 1129808707)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (14484727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (14484727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1129808707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_14484727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1129808707) ^ 564904353 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1129808707) ^ 376602902 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1129808707) ^ 86908362 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1129808707) ^ 78 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1139440259 : Nat.Prime 1139440259 := by
  apply lucas_primality 1139440259 (2 : ZMod 1139440259)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (51792739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (51792739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1139440259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_51792739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1139440259) ^ 569720129 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1139440259) ^ 103585478 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1139440259) ^ 22 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1168068001 : Nat.Prime 1168068001 := by
  apply lucas_primality 1168068001 (31 : ZMod 1168068001)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 3), (11, 1), (8849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 3), (11, 1), (8849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1168068001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_8849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1168068001) ^ 584034000 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (31 : ZMod 1168068001) ^ 389356000 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (31 : ZMod 1168068001) ^ 233613600 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (31 : ZMod 1168068001) ^ 106188000 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (31 : ZMod 1168068001) ^ 132000 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1433381017 : Nat.Prime 1433381017 := by
  apply lucas_primality 1433381017 (7 : ZMod 1433381017)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59724209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59724209, 1)] : List FactorBlock).map factorBlockValue).prod) = 1433381017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_59724209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1433381017) ^ 716690508 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1433381017) ^ 477793672 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1433381017) ^ 24 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1634486779 : Nat.Prime 1634486779 := by
  apply lucas_primality 1634486779 (2 : ZMod 1634486779)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (90804821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (90804821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1634486779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_90804821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1634486779) ^ 817243389 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1634486779) ^ 544828926 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1634486779) ^ 18 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1771538299 : Nat.Prime 1771538299 := by
  apply lucas_primality 1771538299 (2 : ZMod 1771538299)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (659, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (659, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1771538299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_179
      · exact prime_ninetyTwoCL_659
      · exact prime_ninetyTwoCL_2503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1771538299) ^ 885769149 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1771538299) ^ 590512766 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1771538299) ^ 9896862 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1771538299) ^ 2688222 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1771538299) ^ 707766 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1880434267 : Nat.Prime 1880434267 := by
  apply lucas_primality 1880434267 (3 : ZMod 1880434267)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (631, 1), (496681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (631, 1), (496681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1880434267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_631
      · exact prime_ninetyTwoCL_496681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1880434267) ^ 940217133 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1880434267) ^ 626811422 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1880434267) ^ 2980086 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1880434267) ^ 3786 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2027209357 : Nat.Prime 2027209357 := by
  apply lucas_primality 2027209357 (2 : ZMod 2027209357)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (6256819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (6256819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2027209357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_6256819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2027209357) ^ 1013604678 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2027209357) ^ 675736452 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2027209357) ^ 324 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2047919273 : Nat.Prime 2047919273 := by
  apply lucas_primality 2047919273 (3 : ZMod 2047919273)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (1179677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (1179677, 1)] : List FactorBlock).map factorBlockValue).prod) = 2047919273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_31
      · exact prime_ninetyTwoCL_1179677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2047919273) ^ 1023959636 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2047919273) ^ 292559896 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2047919273) ^ 66061912 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2047919273) ^ 1736 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2331866167 : Nat.Prime 2331866167 := by
  apply lucas_primality 2331866167 (5 : ZMod 2331866167)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (1171, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (1171, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) = 2331866167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_1171
      · exact prime_ninetyTwoCL_2789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2331866167) ^ 1165933083 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2331866167) ^ 777288722 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2331866167) ^ 333123738 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2331866167) ^ 137168598 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2331866167) ^ 1991346 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2331866167) ^ 836094 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2337348401 : Nat.Prime 2337348401 := by
  apply lucas_primality 2337348401 (6 : ZMod 2337348401)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (71, 1), (82301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (71, 1), (82301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2337348401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_71
      · exact prime_ninetyTwoCL_82301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2337348401) ^ 1168674200 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2337348401) ^ 467469680 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2337348401) ^ 32920400 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2337348401) ^ 28400 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2392207541 : Nat.Prime 2392207541 := by
  apply lucas_primality 2392207541 (2 : ZMod 2392207541)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (6295283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (6295283, 1)] : List FactorBlock).map factorBlockValue).prod) = 2392207541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_6295283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2392207541) ^ 1196103770 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2392207541) ^ 478441508 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2392207541) ^ 125905660 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2392207541) ^ 380 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2439955649 : Nat.Prime 2439955649 := by
  apply lucas_primality 2439955649 (3 : ZMod 2439955649)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (83, 1), (89, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (83, 1), (89, 1), (397, 1)] : List FactorBlock).map factorBlockValue).prod) = 2439955649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_83
      · exact prime_ninetyTwoCL_89
      · exact prime_ninetyTwoCL_397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2439955649) ^ 1219977824 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2439955649) ^ 187688896 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2439955649) ^ 29397056 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2439955649) ^ 27415232 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2439955649) ^ 6145984 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2440066399 : Nat.Prime 2440066399 := by
  apply lucas_primality 2440066399 (6 : ZMod 2440066399)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 3), (43649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 3), (43649, 1)] : List FactorBlock).map factorBlockValue).prod) = 2440066399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_43649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2440066399) ^ 1220033199 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2440066399) ^ 813355466 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2440066399) ^ 348580914 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2440066399) ^ 221824218 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2440066399) ^ 55902 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2831673541 : Nat.Prime 2831673541 := by
  apply lucas_primality 2831673541 (2 : ZMod 2831673541)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4603, 1), (10253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4603, 1), (10253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2831673541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_4603
      · exact prime_ninetyTwoCL_10253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2831673541) ^ 1415836770 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2831673541) ^ 943891180 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2831673541) ^ 566334708 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2831673541) ^ 615180 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2831673541) ^ 276180 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2838938969 : Nat.Prime 2838938969 := by
  apply lucas_primality 2838938969 (3 : ZMod 2838938969)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9623, 1), (36877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9623, 1), (36877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2838938969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_9623
      · exact prime_ninetyTwoCL_36877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2838938969) ^ 1419469484 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2838938969) ^ 295016 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2838938969) ^ 76984 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2858122733 : Nat.Prime 2858122733 := by
  apply lucas_primality 2858122733 (2 : ZMod 2858122733)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (13481711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (13481711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2858122733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_53
      · exact prime_ninetyTwoCL_13481711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2858122733) ^ 1429061366 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858122733) ^ 53926844 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858122733) ^ 212 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3305345551 : Nat.Prime 3305345551 := by
  apply lucas_primality 3305345551 (3 : ZMod 3305345551)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (31, 1), (54679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (31, 1), (54679, 1)] : List FactorBlock).map factorBlockValue).prod) = 3305345551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_31
      · exact prime_ninetyTwoCL_54679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3305345551) ^ 1652672775 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3305345551) ^ 1101781850 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3305345551) ^ 661069110 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3305345551) ^ 254257350 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3305345551) ^ 106624050 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3305345551) ^ 60450 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3353795293 : Nat.Prime 3353795293 := by
  apply lucas_primality 3353795293 (2 : ZMod 3353795293)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (37, 1), (59, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (37, 1), (59, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 3353795293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_59
      · exact prime_ninetyTwoCL_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3353795293) ^ 1676897646 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3353795293) ^ 1117931764 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3353795293) ^ 197282076 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3353795293) ^ 90643116 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3353795293) ^ 56843988 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3353795293) ^ 7570644 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3600010243 : Nat.Prime 3600010243 := by
  apply lucas_primality 3600010243 (5 : ZMod 3600010243)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (659, 1), (303491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (659, 1), (303491, 1)] : List FactorBlock).map factorBlockValue).prod) = 3600010243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_659
      · exact prime_ninetyTwoCL_303491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3600010243) ^ 1800005121 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3600010243) ^ 1200003414 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3600010243) ^ 5462838 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3600010243) ^ 11862 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3640199267 : Nat.Prime 3640199267 := by
  apply lucas_primality 3640199267 (2 : ZMod 3640199267)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (11903, 1), (13901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (11903, 1), (13901, 1)] : List FactorBlock).map factorBlockValue).prod) = 3640199267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_11903
      · exact prime_ninetyTwoCL_13901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3640199267) ^ 1820099633 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3640199267) ^ 330927206 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3640199267) ^ 305822 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3640199267) ^ 261866 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3808880147 : Nat.Prime 3808880147 := by
  apply lucas_primality 3808880147 (2 : ZMod 3808880147)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (359, 1), (35603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (359, 1), (35603, 1)] : List FactorBlock).map factorBlockValue).prod) = 3808880147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_149
      · exact prime_ninetyTwoCL_359
      · exact prime_ninetyTwoCL_35603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3808880147) ^ 1904440073 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3808880147) ^ 25562954 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3808880147) ^ 10609694 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3808880147) ^ 106982 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4171548949 : Nat.Prime 4171548949 := by
  apply lucas_primality 4171548949 (6 : ZMod 4171548949)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (7094471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (7094471, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171548949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_7094471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4171548949) ^ 2085774474 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4171548949) ^ 1390516316 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4171548949) ^ 595935564 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4171548949) ^ 588 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4485381079 : Nat.Prime 4485381079 := by
  apply lucas_primality 4485381079 (3 : ZMod 4485381079)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (929, 1), (804697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (929, 1), (804697, 1)] : List FactorBlock).map factorBlockValue).prod) = 4485381079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_929
      · exact prime_ninetyTwoCL_804697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4485381079) ^ 2242690539 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4485381079) ^ 1495127026 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4485381079) ^ 4828182 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4485381079) ^ 5574 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4576121681 : Nat.Prime 4576121681 := by
  apply lucas_primality 4576121681 (3 : ZMod 4576121681)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (787, 1), (5591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (787, 1), (5591, 1)] : List FactorBlock).map factorBlockValue).prod) = 4576121681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_787
      · exact prime_ninetyTwoCL_5591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4576121681) ^ 2288060840 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4576121681) ^ 915224336 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4576121681) ^ 352009360 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4576121681) ^ 5814640 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4576121681) ^ 818480 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4867087447 : Nat.Prime 4867087447 := by
  apply lucas_primality 4867087447 (3 : ZMod 4867087447)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 2), (533321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 2), (533321, 1)] : List FactorBlock).map factorBlockValue).prod) = 4867087447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_533321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4867087447) ^ 2433543723 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4867087447) ^ 1622362482 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4867087447) ^ 374391342 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4867087447) ^ 9126 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_5547451051 : Nat.Prime 5547451051 := by
  apply lucas_primality 5547451051 (2 : ZMod 5547451051)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (17, 1), (197, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (17, 1), (197, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5547451051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_197
      · exact prime_ninetyTwoCL_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5547451051) ^ 2773725525 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547451051) ^ 1849150350 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547451051) ^ 1109490210 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547451051) ^ 326320650 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547451051) ^ 28159650 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5547451051) ^ 13563450 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_5918085049 : Nat.Prime 5918085049 := by
  apply lucas_primality 5918085049 (13 : ZMod 5918085049)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (246586877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (246586877, 1)] : List FactorBlock).map factorBlockValue).prod) = 5918085049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_246586877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 5918085049) ^ 2959042524 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 5918085049) ^ 1972695016 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 5918085049) ^ 24 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_6097055581 : Nat.Prime 6097055581 := by
  apply lucas_primality 6097055581 (2 : ZMod 6097055581)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (439903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (439903, 1)] : List FactorBlock).map factorBlockValue).prod) = 6097055581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_439903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6097055581) ^ 3048527790 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6097055581) ^ 2032351860 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6097055581) ^ 1219411116 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6097055581) ^ 871007940 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6097055581) ^ 554277780 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6097055581) ^ 13860 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_6185768929 : Nat.Prime 6185768929 := by
  apply lucas_primality 6185768929 (11 : ZMod 6185768929)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (37, 1), (61, 1), (28549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (37, 1), (61, 1), (28549, 1)] : List FactorBlock).map factorBlockValue).prod) = 6185768929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_61
      · exact prime_ninetyTwoCL_28549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6185768929) ^ 3092884464 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 6185768929) ^ 2061922976 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 6185768929) ^ 167182944 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 6185768929) ^ 101406048 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 6185768929) ^ 216672 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_7973398841 : Nat.Prime 7973398841 := by
  apply lucas_primality 7973398841 (3 : ZMod 7973398841)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (43, 1), (131, 1), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (43, 1), (131, 1), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) = 7973398841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_43
      · exact prime_ninetyTwoCL_131
      · exact prime_ninetyTwoCL_3217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7973398841) ^ 3986699420 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7973398841) ^ 1594679768 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7973398841) ^ 724854440 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7973398841) ^ 185427880 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7973398841) ^ 60865640 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7973398841) ^ 2478520 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_8197277839 : Nat.Prime 8197277839 := by
  apply lucas_primality 8197277839 (11 : ZMod 8197277839)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (211, 1), (380879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (211, 1), (380879, 1)] : List FactorBlock).map factorBlockValue).prod) = 8197277839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_211
      · exact prime_ninetyTwoCL_380879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8197277839) ^ 4098638919 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8197277839) ^ 2732425946 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8197277839) ^ 482192814 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8197277839) ^ 38849658 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 8197277839) ^ 21522 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_8651478937 : Nat.Prime 8651478937 := by
  apply lucas_primality 8651478937 (5 : ZMod 8651478937)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (71, 1), (229, 1), (22171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (71, 1), (229, 1), (22171, 1)] : List FactorBlock).map factorBlockValue).prod) = 8651478937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_71
      · exact prime_ninetyTwoCL_229
      · exact prime_ninetyTwoCL_22171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8651478937) ^ 4325739468 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8651478937) ^ 2883826312 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8651478937) ^ 121851816 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8651478937) ^ 37779384 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8651478937) ^ 390216 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_10425905323 : Nat.Prime 10425905323 := by
  apply lucas_primality 10425905323 (2 : ZMod 10425905323)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (35462263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (35462263, 1)] : List FactorBlock).map factorBlockValue).prod) = 10425905323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_35462263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10425905323) ^ 5212952661 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10425905323) ^ 3475301774 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10425905323) ^ 1489415046 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10425905323) ^ 294 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_10618311727 : Nat.Prime 10618311727 := by
  apply lucas_primality 10618311727 (3 : ZMod 10618311727)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (37, 2), (43, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (37, 2), (43, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 10618311727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_43
      · exact prime_ninetyTwoCL_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10618311727) ^ 5309155863 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10618311727) ^ 3539437242 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10618311727) ^ 965301066 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10618311727) ^ 286981398 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10618311727) ^ 246937482 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10618311727) ^ 11655666 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_11895939929 : Nat.Prime 11895939929 := by
  apply lucas_primality 11895939929 (3 : ZMod 11895939929)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (191, 1), (257, 1), (30293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (191, 1), (257, 1), (30293, 1)] : List FactorBlock).map factorBlockValue).prod) = 11895939929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_191
      · exact prime_ninetyTwoCL_257
      · exact prime_ninetyTwoCL_30293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11895939929) ^ 5947969964 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11895939929) ^ 62282408 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11895939929) ^ 46287704 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11895939929) ^ 392696 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_12773596993 : Nat.Prime 12773596993 := by
  apply lucas_primality 12773596993 (7 : ZMod 12773596993)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 1), (53, 1), (223, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 1), (53, 1), (223, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) = 12773596993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_53
      · exact prime_ninetyTwoCL_223
      · exact prime_ninetyTwoCL_433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12773596993) ^ 6386798496 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 12773596993) ^ 4257865664 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 12773596993) ^ 982584384 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 12773596993) ^ 241011264 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 12773596993) ^ 57280704 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 12773596993) ^ 29500224 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_13688863073 : Nat.Prime 13688863073 := by
  apply lucas_primality 13688863073 (3 : ZMod 13688863073)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (563, 1), (673, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (563, 1), (673, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 13688863073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_563
      · exact prime_ninetyTwoCL_673
      · exact prime_ninetyTwoCL_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13688863073) ^ 6844431536 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13688863073) ^ 24314144 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13688863073) ^ 20340064 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13688863073) ^ 12124768 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_14024090407 : Nat.Prime 14024090407 := by
  apply lucas_primality 14024090407 (3 : ZMod 14024090407)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2337348401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2337348401, 1)] : List FactorBlock).map factorBlockValue).prod) = 14024090407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_2337348401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14024090407) ^ 7012045203 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14024090407) ^ 4674696802 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14024090407) ^ 6 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_15814651201 : Nat.Prime 15814651201 := by
  apply lucas_primality 15814651201 (7 : ZMod 15814651201)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (17, 1), (29, 1), (41, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (17, 1), (29, 1), (41, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 15814651201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15814651201) ^ 7907325600 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 15814651201) ^ 5271550400 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 15814651201) ^ 3162930240 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 15814651201) ^ 930273600 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 15814651201) ^ 545332800 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 15814651201) ^ 385723200 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 15814651201) ^ 97022400 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_16783013141 : Nat.Prime 16783013141 := by
  apply lucas_primality 16783013141 (3 : ZMod 16783013141)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1993, 1), (421049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1993, 1), (421049, 1)] : List FactorBlock).map factorBlockValue).prod) = 16783013141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_1993
      · exact prime_ninetyTwoCL_421049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16783013141) ^ 8391506570 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 16783013141) ^ 3356602628 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 16783013141) ^ 8420980 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 16783013141) ^ 39860 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_17097069221 : Nat.Prime 17097069221 := by
  apply lucas_primality 17097069221 (3 : ZMod 17097069221)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (11, 1), (167, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (11, 1), (167, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod) = 17097069221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_167
      · exact prime_ninetyTwoCL_9497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17097069221) ^ 8548534610 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 17097069221) ^ 3419413844 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 17097069221) ^ 2442438460 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 17097069221) ^ 1554279020 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 17097069221) ^ 102377660 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 17097069221) ^ 1800260 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_17192452609 : Nat.Prime 17192452609 := by
  apply lucas_primality 17192452609 (7 : ZMod 17192452609)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 3), (47, 2), (563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 3), (47, 2), (563, 1)] : List FactorBlock).map factorBlockValue).prod) = 17192452609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_47
      · exact prime_ninetyTwoCL_563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17192452609) ^ 8596226304 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 17192452609) ^ 5730817536 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 17192452609) ^ 365796864 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 17192452609) ^ 30537216 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_20953581563 : Nat.Prime 20953581563 := by
  apply lucas_primality 20953581563 (2 : ZMod 20953581563)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30187, 1), (347063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30187, 1), (347063, 1)] : List FactorBlock).map factorBlockValue).prod) = 20953581563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_30187
      · exact prime_ninetyTwoCL_347063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20953581563) ^ 10476790781 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20953581563) ^ 694126 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20953581563) ^ 60374 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_24181385651 : Nat.Prime 24181385651 := by
  apply lucas_primality 24181385651 (2 : ZMod 24181385651)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (28448689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (28448689, 1)] : List FactorBlock).map factorBlockValue).prod) = 24181385651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_28448689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24181385651) ^ 12090692825 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24181385651) ^ 4836277130 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24181385651) ^ 1422434450 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24181385651) ^ 850 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_24674759119 : Nat.Prime 24674759119 := by
  apply lucas_primality 24674759119 (3 : ZMod 24674759119)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (9643, 1), (142157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (9643, 1), (142157, 1)] : List FactorBlock).map factorBlockValue).prod) = 24674759119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_9643
      · exact prime_ninetyTwoCL_142157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24674759119) ^ 12337379559 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24674759119) ^ 8224919706 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24674759119) ^ 2558826 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24674759119) ^ 173574 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_34832995957 : Nat.Prime 34832995957 := by
  apply lucas_primality 34832995957 (5 : ZMod 34832995957)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (317, 1), (277483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (317, 1), (277483, 1)] : List FactorBlock).map factorBlockValue).prod) = 34832995957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_317
      · exact prime_ninetyTwoCL_277483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34832995957) ^ 17416497978 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 34832995957) ^ 11610998652 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 34832995957) ^ 3166635996 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 34832995957) ^ 109883268 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 34832995957) ^ 125532 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_45033394529 : Nat.Prime 45033394529 := by
  apply lucas_primality 45033394529 (3 : ZMod 45033394529)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5557, 1), (253247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5557, 1), (253247, 1)] : List FactorBlock).map factorBlockValue).prod) = 45033394529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5557
      · exact prime_ninetyTwoCL_253247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 45033394529) ^ 22516697264 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 45033394529) ^ 8103904 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 45033394529) ^ 177824 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_59217934261 : Nat.Prime 59217934261 := by
  apply lucas_primality 59217934261 (13 : ZMod 59217934261)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (41, 1), (24072331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (41, 1), (24072331, 1)] : List FactorBlock).map factorBlockValue).prod) = 59217934261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_24072331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 59217934261) ^ 29608967130 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 59217934261) ^ 19739311420 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 59217934261) ^ 11843586852 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 59217934261) ^ 1444339860 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 59217934261) ^ 2460 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_69136712017 : Nat.Prime 69136712017 := by
  apply lucas_primality 69136712017 (10 : ZMod 69136712017)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (263, 1), (127363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (263, 1), (127363, 1)] : List FactorBlock).map factorBlockValue).prod) = 69136712017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_43
      · exact prime_ninetyTwoCL_263
      · exact prime_ninetyTwoCL_127363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 69136712017) ^ 34568356008 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 69136712017) ^ 23045570672 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 69136712017) ^ 1607830512 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 69136712017) ^ 262877232 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 69136712017) ^ 542832 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_75958138367 : Nat.Prime 75958138367 := by
  apply lucas_primality 75958138367 (5 : ZMod 75958138367)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (53, 1), (59, 1), (1104139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (53, 1), (59, 1), (1104139, 1)] : List FactorBlock).map factorBlockValue).prod) = 75958138367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_53
      · exact prime_ninetyTwoCL_59
      · exact prime_ninetyTwoCL_1104139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 75958138367) ^ 37979069183 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75958138367) ^ 6905285306 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75958138367) ^ 1433172422 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75958138367) ^ 1287426074 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75958138367) ^ 68794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_76723720261 : Nat.Prime 76723720261 := by
  apply lucas_primality 76723720261 (28 : ZMod 76723720261)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (19, 1), (47, 1), (349, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (19, 1), (47, 1), (349, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 76723720261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_47
      · exact prime_ninetyTwoCL_349
      · exact prime_ninetyTwoCL_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (28 : ZMod 76723720261) ^ 38361860130 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (28 : ZMod 76723720261) ^ 25574573420 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (28 : ZMod 76723720261) ^ 15344744052 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (28 : ZMod 76723720261) ^ 6974883660 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (28 : ZMod 76723720261) ^ 4038090540 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (28 : ZMod 76723720261) ^ 1632419580 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (28 : ZMod 76723720261) ^ 219838740 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (28 : ZMod 76723720261) ^ 205693620 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_80269493789 : Nat.Prime 80269493789 := by
  apply lucas_primality 80269493789 (2 : ZMod 80269493789)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (5981, 1), (305017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (5981, 1), (305017, 1)] : List FactorBlock).map factorBlockValue).prod) = 80269493789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_5981
      · exact prime_ninetyTwoCL_305017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80269493789) ^ 40134746894 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 80269493789) ^ 7297226708 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 80269493789) ^ 13420748 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 80269493789) ^ 263164 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_82770882941 : Nat.Prime 82770882941 := by
  apply lucas_primality 82770882941 (2 : ZMod 82770882941)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (2069, 1), (105277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (2069, 1), (105277, 1)] : List FactorBlock).map factorBlockValue).prod) = 82770882941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_2069
      · exact prime_ninetyTwoCL_105277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82770882941) ^ 41385441470 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 82770882941) ^ 16554176588 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 82770882941) ^ 4356362260 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 82770882941) ^ 40005260 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 82770882941) ^ 786220 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_88534873213 : Nat.Prime 88534873213 := by
  apply lucas_primality 88534873213 (2 : ZMod 88534873213)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (237996971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (237996971, 1)] : List FactorBlock).map factorBlockValue).prod) = 88534873213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_31
      · exact prime_ninetyTwoCL_237996971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88534873213) ^ 44267436606 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 88534873213) ^ 29511624404 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 88534873213) ^ 2855963652 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 88534873213) ^ 372 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_104259053231 : Nat.Prime 104259053231 := by
  apply lucas_primality 104259053231 (7 : ZMod 104259053231)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10425905323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10425905323, 1)] : List FactorBlock).map factorBlockValue).prod) = 104259053231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_10425905323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 104259053231) ^ 52129526615 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 104259053231) ^ 20851810646 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 104259053231) ^ 10 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_104547223661 : Nat.Prime 104547223661 := by
  apply lucas_primality 104547223661 (7 : ZMod 104547223661)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (475214653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (475214653, 1)] : List FactorBlock).map factorBlockValue).prod) = 104547223661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_475214653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 104547223661) ^ 52273611830 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 104547223661) ^ 20909444732 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 104547223661) ^ 9504293060 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 104547223661) ^ 220 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_122019340357 : Nat.Prime 122019340357 := by
  apply lucas_primality 122019340357 (5 : ZMod 122019340357)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1129808707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1129808707, 1)] : List FactorBlock).map factorBlockValue).prod) = 122019340357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_1129808707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 122019340357) ^ 61009670178 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 122019340357) ^ 40673113452 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 122019340357) ^ 108 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_127237469683 : Nat.Prime 127237469683 := by
  apply lucas_primality 127237469683 (2 : ZMod 127237469683)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (451196701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (451196701, 1)] : List FactorBlock).map factorBlockValue).prod) = 127237469683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_47
      · exact prime_ninetyTwoCL_451196701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 127237469683) ^ 63618734841 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 127237469683) ^ 42412489894 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 127237469683) ^ 2707180206 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 127237469683) ^ 282 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_134572402463 : Nat.Prime 134572402463 := by
  apply lucas_primality 134572402463 (5 : ZMod 134572402463)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (439, 1), (794153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (439, 1), (794153, 1)] : List FactorBlock).map factorBlockValue).prod) = 134572402463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_193
      · exact prime_ninetyTwoCL_439
      · exact prime_ninetyTwoCL_794153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 134572402463) ^ 67286201231 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 134572402463) ^ 697266334 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 134572402463) ^ 306543058 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 134572402463) ^ 169454 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_137867489647 : Nat.Prime 137867489647 := by
  apply lucas_primality 137867489647 (6 : ZMod 137867489647)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (599, 1), (38360459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (599, 1), (38360459, 1)] : List FactorBlock).map factorBlockValue).prod) = 137867489647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_599
      · exact prime_ninetyTwoCL_38360459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 137867489647) ^ 68933744823 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 137867489647) ^ 45955829882 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 137867489647) ^ 230162754 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 137867489647) ^ 3594 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_188636100379 : Nat.Prime 188636100379 := by
  apply lucas_primality 188636100379 (11 : ZMod 188636100379)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2858122733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2858122733, 1)] : List FactorBlock).map factorBlockValue).prod) = 188636100379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_2858122733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 188636100379) ^ 94318050189 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 188636100379) ^ 62878700126 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 188636100379) ^ 17148736398 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 188636100379) ^ 66 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_200309462473 : Nat.Prime 200309462473 := by
  apply lucas_primality 200309462473 (5 : ZMod 200309462473)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19, 1), (23, 1), (37, 2), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19, 1), (23, 1), (37, 2), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) = 200309462473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_1993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 200309462473) ^ 100154731236 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 200309462473) ^ 66769820824 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 200309462473) ^ 28615637496 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 200309462473) ^ 10542603288 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 200309462473) ^ 8709107064 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 200309462473) ^ 5413769256 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 200309462473) ^ 100506504 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_242050823381 : Nat.Prime 242050823381 := by
  apply lucas_primality 242050823381 (2 : ZMod 242050823381)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (636975851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (636975851, 1)] : List FactorBlock).map factorBlockValue).prod) = 242050823381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_636975851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 242050823381) ^ 121025411690 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 242050823381) ^ 48410164676 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 242050823381) ^ 12739517020 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 242050823381) ^ 380 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_242241410237 : Nat.Prime 242241410237 := by
  apply lucas_primality 242241410237 (3 : ZMod 242241410237)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (8651478937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (8651478937, 1)] : List FactorBlock).map factorBlockValue).prod) = 242241410237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_8651478937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 242241410237) ^ 121120705118 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 242241410237) ^ 34605915748 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 242241410237) ^ 28 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_248269371839 : Nat.Prime 248269371839 := by
  apply lucas_primality 248269371839 (11 : ZMod 248269371839)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (33811, 1), (126601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (33811, 1), (126601, 1)] : List FactorBlock).map factorBlockValue).prod) = 248269371839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_33811
      · exact prime_ninetyTwoCL_126601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 248269371839) ^ 124134685919 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 248269371839) ^ 8561012822 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 248269371839) ^ 7342858 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 248269371839) ^ 1961038 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_296393412331 : Nat.Prime 296393412331 := by
  apply lucas_primality 296393412331 (3 : ZMod 296393412331)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (541, 1), (676373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (541, 1), (676373, 1)] : List FactorBlock).map factorBlockValue).prod) = 296393412331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_541
      · exact prime_ninetyTwoCL_676373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 296393412331) ^ 148196706165 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 296393412331) ^ 98797804110 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 296393412331) ^ 59278682466 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 296393412331) ^ 547862130 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 296393412331) ^ 438210 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_304081403551 : Nat.Prime 304081403551 := by
  apply lucas_primality 304081403551 (3 : ZMod 304081403551)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (2027209357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (2027209357, 1)] : List FactorBlock).map factorBlockValue).prod) = 304081403551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_2027209357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 304081403551) ^ 152040701775 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 304081403551) ^ 101360467850 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 304081403551) ^ 60816280710 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 304081403551) ^ 150 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_346275200449 : Nat.Prime 346275200449 := by
  apply lucas_primality 346275200449 (7 : ZMod 346275200449)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (151, 1), (1327091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (151, 1), (1327091, 1)] : List FactorBlock).map factorBlockValue).prod) = 346275200449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_151
      · exact prime_ninetyTwoCL_1327091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 346275200449) ^ 173137600224 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 346275200449) ^ 115425066816 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 346275200449) ^ 2293213248 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 346275200449) ^ 260928 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_399703870003 : Nat.Prime 399703870003 := by
  apply lucas_primality 399703870003 (3 : ZMod 399703870003)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1097, 1), (60726811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1097, 1), (60726811, 1)] : List FactorBlock).map factorBlockValue).prod) = 399703870003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_1097
      · exact prime_ninetyTwoCL_60726811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 399703870003) ^ 199851935001 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 399703870003) ^ 133234623334 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 399703870003) ^ 364360866 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 399703870003) ^ 6582 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_425721474097 : Nat.Prime 425721474097 := by
  apply lucas_primality 425721474097 (5 : ZMod 425721474097)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (349, 1), (1319, 1), (19267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (349, 1), (1319, 1), (19267, 1)] : List FactorBlock).map factorBlockValue).prod) = 425721474097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_349
      · exact prime_ninetyTwoCL_1319
      · exact prime_ninetyTwoCL_19267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 425721474097) ^ 212860737048 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 425721474097) ^ 141907158032 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 425721474097) ^ 1219832304 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 425721474097) ^ 322760784 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 425721474097) ^ 22095888 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_460342321567 : Nat.Prime 460342321567 := by
  apply lucas_primality 460342321567 (3 : ZMod 460342321567)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (76723720261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (76723720261, 1)] : List FactorBlock).map factorBlockValue).prod) = 460342321567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_76723720261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 460342321567) ^ 230171160783 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 460342321567) ^ 153447440522 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 460342321567) ^ 6 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_557065281833 : Nat.Prime 557065281833 := by
  apply lucas_primality 557065281833 (3 : ZMod 557065281833)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (174901, 1), (398129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (174901, 1), (398129, 1)] : List FactorBlock).map factorBlockValue).prod) = 557065281833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_174901
      · exact prime_ninetyTwoCL_398129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 557065281833) ^ 278532640916 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 557065281833) ^ 3185032 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 557065281833) ^ 1399208 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_692437802773 : Nat.Prime 692437802773 := by
  apply lucas_primality 692437802773 (5 : ZMod 692437802773)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (359, 1), (419, 1), (383611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (359, 1), (419, 1), (383611, 1)] : List FactorBlock).map factorBlockValue).prod) = 692437802773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_359
      · exact prime_ninetyTwoCL_419
      · exact prime_ninetyTwoCL_383611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 692437802773) ^ 346218901386 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 692437802773) ^ 230812600924 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 692437802773) ^ 1928796108 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 692437802773) ^ 1652596188 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 692437802773) ^ 1805052 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_781998880037 : Nat.Prime 781998880037 := by
  apply lucas_primality 781998880037 (2 : ZMod 781998880037)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (107, 1), (263, 1), (631559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (107, 1), (263, 1), (631559, 1)] : List FactorBlock).map factorBlockValue).prod) = 781998880037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_107
      · exact prime_ninetyTwoCL_263
      · exact prime_ninetyTwoCL_631559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 781998880037) ^ 390999440018 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 781998880037) ^ 71090807276 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 781998880037) ^ 7308400748 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 781998880037) ^ 2973379772 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 781998880037) ^ 1238204 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1040608410329 : Nat.Prime 1040608410329 := by
  apply lucas_primality 1040608410329 (3 : ZMod 1040608410329)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (4485381079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (4485381079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1040608410329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_4485381079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1040608410329) ^ 520304205164 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1040608410329) ^ 35883048632 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1040608410329) ^ 232 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1447469929387 : Nat.Prime 1447469929387 := by
  apply lucas_primality 1447469929387 (2 : ZMod 1447469929387)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (6185768929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (6185768929, 1)] : List FactorBlock).map factorBlockValue).prod) = 1447469929387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_6185768929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1447469929387) ^ 723734964693 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1447469929387) ^ 482489976462 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1447469929387) ^ 111343840722 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1447469929387) ^ 234 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1455399207503 : Nat.Prime 1455399207503 := by
  apply lucas_primality 1455399207503 (5 : ZMod 1455399207503)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (397, 1), (31067737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (397, 1), (31067737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1455399207503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_59
      · exact prime_ninetyTwoCL_397
      · exact prime_ninetyTwoCL_31067737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1455399207503) ^ 727699603751 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455399207503) ^ 24667783178 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455399207503) ^ 3665992966 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455399207503) ^ 46846 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1806264798787 : Nat.Prime 1806264798787 := by
  apply lucas_primality 1806264798787 (2 : ZMod 1806264798787)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (2047919273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (2047919273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1806264798787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_2047919273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1806264798787) ^ 903132399393 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806264798787) ^ 602088266262 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806264798787) ^ 258037828398 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806264798787) ^ 882 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1812993343717 : Nat.Prime 1812993343717 := by
  apply lucas_primality 1812993343717 (5 : ZMod 1812993343717)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (97, 1), (25533679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (97, 1), (25533679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1812993343717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_61
      · exact prime_ninetyTwoCL_97
      · exact prime_ninetyTwoCL_25533679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1812993343717) ^ 906496671858 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1812993343717) ^ 604331114572 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1812993343717) ^ 29721202356 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1812993343717) ^ 18690653028 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1812993343717) ^ 71004 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2381492125087 : Nat.Prime 2381492125087 := by
  apply lucas_primality 2381492125087 (3 : ZMod 2381492125087)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (509, 1), (41041811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (509, 1), (41041811, 1)] : List FactorBlock).map factorBlockValue).prod) = 2381492125087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_509
      · exact prime_ninetyTwoCL_41041811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2381492125087) ^ 1190746062543 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381492125087) ^ 793830708362 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381492125087) ^ 125341690794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381492125087) ^ 4678766454 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2381492125087) ^ 58026 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3523361437663 : Nat.Prime 3523361437663 := by
  apply lucas_primality 3523361437663 (5 : ZMod 3523361437663)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (127979, 1), (417133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (127979, 1), (417133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3523361437663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_127979
      · exact prime_ninetyTwoCL_417133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3523361437663) ^ 1761680718831 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3523361437663) ^ 1174453812554 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3523361437663) ^ 320305585242 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3523361437663) ^ 27530778 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3523361437663) ^ 8446614 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3679669251257 : Nat.Prime 3679669251257 := by
  apply lucas_primality 3679669251257 (3 : ZMod 3679669251257)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89611, 1), (5132837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89611, 1), (5132837, 1)] : List FactorBlock).map factorBlockValue).prod) = 3679669251257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_89611
      · exact prime_ninetyTwoCL_5132837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3679669251257) ^ 1839834625628 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3679669251257) ^ 41062696 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3679669251257) ^ 716888 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4367553929411 : Nat.Prime 4367553929411 := by
  apply lucas_primality 4367553929411 (6 : ZMod 4367553929411)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (62327, 1), (1001069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (62327, 1), (1001069, 1)] : List FactorBlock).map factorBlockValue).prod) = 4367553929411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_62327
      · exact prime_ninetyTwoCL_1001069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4367553929411) ^ 2183776964705 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4367553929411) ^ 873510785882 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4367553929411) ^ 623936275630 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4367553929411) ^ 70074830 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 4367553929411) ^ 4362890 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4400109646951 : Nat.Prime 4400109646951 := by
  apply lucas_primality 4400109646951 (3 : ZMod 4400109646951)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (37, 1), (5171, 1), (153319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (37, 1), (5171, 1), (153319, 1)] : List FactorBlock).map factorBlockValue).prod) = 4400109646951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_5171
      · exact prime_ninetyTwoCL_153319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4400109646951) ^ 2200054823475 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4400109646951) ^ 1466703215650 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4400109646951) ^ 880021929390 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4400109646951) ^ 118921882350 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4400109646951) ^ 850920450 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4400109646951) ^ 28699050 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_6149844382471 : Nat.Prime 6149844382471 := by
  apply lucas_primality 6149844382471 (3 : ZMod 6149844382471)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (634658863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (634658863, 1)] : List FactorBlock).map factorBlockValue).prod) = 6149844382471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_634658863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6149844382471) ^ 3074922191235 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6149844382471) ^ 2049948127490 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6149844382471) ^ 1229968876494 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6149844382471) ^ 361755551910 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6149844382471) ^ 323676020130 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6149844382471) ^ 9690 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_6180747490607 : Nat.Prime 6180747490607 := by
  apply lucas_primality 6180747490607 (5 : ZMod 6180747490607)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (8197277839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (8197277839, 1)] : List FactorBlock).map factorBlockValue).prod) = 6180747490607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_8197277839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6180747490607) ^ 3090373745303 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 6180747490607) ^ 475442114662 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 6180747490607) ^ 213129223814 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 6180747490607) ^ 754 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_8453554344407 : Nat.Prime 8453554344407 := by
  apply lucas_primality 8453554344407 (5 : ZMod 8453554344407)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12227, 1), (345692089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12227, 1), (345692089, 1)] : List FactorBlock).map factorBlockValue).prod) = 8453554344407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_12227
      · exact prime_ninetyTwoCL_345692089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8453554344407) ^ 4226777172203 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8453554344407) ^ 691384178 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8453554344407) ^ 24454 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_10985267052779 : Nat.Prime 10985267052779 := by
  apply lucas_primality 10985267052779 (2 : ZMod 10985267052779)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12037, 1), (456312497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12037, 1), (456312497, 1)] : List FactorBlock).map factorBlockValue).prod) = 10985267052779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_12037
      · exact prime_ninetyTwoCL_456312497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10985267052779) ^ 5492633526389 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10985267052779) ^ 912624994 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10985267052779) ^ 24074 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_11100846842429 : Nat.Prime 11100846842429 := by
  apply lucas_primality 11100846842429 (2 : ZMod 11100846842429)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (460079, 1), (861719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (460079, 1), (861719, 1)] : List FactorBlock).map factorBlockValue).prod) = 11100846842429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_460079
      · exact prime_ninetyTwoCL_861719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11100846842429) ^ 5550423421214 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11100846842429) ^ 1585835263204 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11100846842429) ^ 24128132 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11100846842429) ^ 12882212 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_14304198793403 : Nat.Prime 14304198793403 := by
  apply lucas_primality 14304198793403 (2 : ZMod 14304198793403)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4943, 1), (206702101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4943, 1), (206702101, 1)] : List FactorBlock).map factorBlockValue).prod) = 14304198793403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_4943
      · exact prime_ninetyTwoCL_206702101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14304198793403) ^ 7152099396701 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14304198793403) ^ 2043456970486 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14304198793403) ^ 2893829414 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14304198793403) ^ 69202 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_15425550619931 : Nat.Prime 15425550619931 := by
  apply lucas_primality 15425550619931 (6 : ZMod 15425550619931)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (23, 1), (6097055581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (23, 1), (6097055581, 1)] : List FactorBlock).map factorBlockValue).prod) = 15425550619931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_6097055581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15425550619931) ^ 7712775309965 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 15425550619931) ^ 3085110123986 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 15425550619931) ^ 1402322783630 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 15425550619931) ^ 670676113910 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 15425550619931) ^ 2530 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_18480348456667 : Nat.Prime 18480348456667 := by
  apply lucas_primality 18480348456667 (3 : ZMod 18480348456667)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71161, 1), (43282951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71161, 1), (43282951, 1)] : List FactorBlock).map factorBlockValue).prod) = 18480348456667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_71161
      · exact prime_ninetyTwoCL_43282951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18480348456667) ^ 9240174228333 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18480348456667) ^ 6160116152222 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18480348456667) ^ 259697706 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18480348456667) ^ 426966 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_18843762834121 : Nat.Prime 18843762834121 := by
  apply lucas_primality 18843762834121 (58 : ZMod 18843762834121)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (9623, 1), (2331191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (9623, 1), (2331191, 1)] : List FactorBlock).map factorBlockValue).prod) = 18843762834121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_9623
      · exact prime_ninetyTwoCL_2331191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (58 : ZMod 18843762834121) ^ 9421881417060 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (58 : ZMod 18843762834121) ^ 6281254278040 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (58 : ZMod 18843762834121) ^ 3768752566824 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (58 : ZMod 18843762834121) ^ 2691966119160 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (58 : ZMod 18843762834121) ^ 1958200440 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (58 : ZMod 18843762834121) ^ 8083320 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_49622613176371 : Nat.Prime 49622613176371 := by
  apply lucas_primality 49622613176371 (2 : ZMod 49622613176371)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (127237469683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (127237469683, 1)] : List FactorBlock).map factorBlockValue).prod) = 49622613176371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_127237469683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49622613176371) ^ 24811306588185 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49622613176371) ^ 16540871058790 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49622613176371) ^ 9924522635274 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49622613176371) ^ 3817124090490 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49622613176371) ^ 390 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_50067838215211 : Nat.Prime 50067838215211 := by
  apply lucas_primality 50067838215211 (2 : ZMod 50067838215211)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (2939, 1), (7188047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (2939, 1), (7188047, 1)] : List FactorBlock).map factorBlockValue).prod) = 50067838215211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_79
      · exact prime_ninetyTwoCL_2939
      · exact prime_ninetyTwoCL_7188047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50067838215211) ^ 25033919107605 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50067838215211) ^ 16689279405070 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50067838215211) ^ 10013567643042 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50067838215211) ^ 633770103990 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50067838215211) ^ 17035671390 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50067838215211) ^ 6965430 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_54413802411097 : Nat.Prime 54413802411097 := by
  apply lucas_primality 54413802411097 (5 : ZMod 54413802411097)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (379, 1), (479, 1), (337537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (379, 1), (479, 1), (337537, 1)] : List FactorBlock).map factorBlockValue).prod) = 54413802411097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_379
      · exact prime_ninetyTwoCL_479
      · exact prime_ninetyTwoCL_337537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54413802411097) ^ 27206901205548 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 54413802411097) ^ 18137934137032 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 54413802411097) ^ 1470643308408 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 54413802411097) ^ 143572038024 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 54413802411097) ^ 113598752424 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 54413802411097) ^ 161208408 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_71703457430153 : Nat.Prime 71703457430153 := by
  apply lucas_primality 71703457430153 (3 : ZMod 71703457430153)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (242241410237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (242241410237, 1)] : List FactorBlock).map factorBlockValue).prod) = 71703457430153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_242241410237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71703457430153) ^ 35851728715076 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 71703457430153) ^ 1937931281896 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 71703457430153) ^ 296 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_85892253428087 : Nat.Prime 85892253428087 := by
  apply lucas_primality 85892253428087 (5 : ZMod 85892253428087)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1103, 1), (1889, 1), (2944547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1103, 1), (1889, 1), (2944547, 1)] : List FactorBlock).map factorBlockValue).prod) = 85892253428087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_1103
      · exact prime_ninetyTwoCL_1889
      · exact prime_ninetyTwoCL_2944547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 85892253428087) ^ 42946126714043 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85892253428087) ^ 12270321918298 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85892253428087) ^ 77871489962 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85892253428087) ^ 45469694774 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 85892253428087) ^ 29169938 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_95649965981281 : Nat.Prime 95649965981281 := by
  apply lucas_primality 95649965981281 (7 : ZMod 95649965981281)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (197, 1), (112391857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (197, 1), (112391857, 1)] : List FactorBlock).map factorBlockValue).prod) = 95649965981281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_197
      · exact prime_ninetyTwoCL_112391857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 95649965981281) ^ 47824982990640 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 95649965981281) ^ 31883321993760 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 95649965981281) ^ 19129993196256 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 95649965981281) ^ 485532822240 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 95649965981281) ^ 851040 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_97474288137229 : Nat.Prime 97474288137229 := by
  apply lucas_primality 97474288137229 (2 : ZMod 97474288137229)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (18731, 1), (144552833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (18731, 1), (144552833, 1)] : List FactorBlock).map factorBlockValue).prod) = 97474288137229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_18731
      · exact prime_ninetyTwoCL_144552833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97474288137229) ^ 48737144068614 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 97474288137229) ^ 32491429379076 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 97474288137229) ^ 5203901988 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 97474288137229) ^ 674316 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_143698279199197 : Nat.Prime 143698279199197 := by
  apply lucas_primality 143698279199197 (2 : ZMod 143698279199197)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 1), (10099, 1), (11740067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 1), (10099, 1), (11740067, 1)] : List FactorBlock).map factorBlockValue).prod) = 143698279199197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_101
      · exact prime_ninetyTwoCL_10099
      · exact prime_ninetyTwoCL_11740067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 143698279199197) ^ 71849139599598 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 143698279199197) ^ 47899426399732 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 143698279199197) ^ 1422755239596 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 143698279199197) ^ 14228961204 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 143698279199197) ^ 12239988 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_150467649000299 : Nat.Prime 150467649000299 := by
  apply lucas_primality 150467649000299 (6 : ZMod 150467649000299)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (402613, 1), (26694839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (402613, 1), (26694839, 1)] : List FactorBlock).map factorBlockValue).prod) = 150467649000299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_402613
      · exact prime_ninetyTwoCL_26694839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 150467649000299) ^ 75233824500149 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 150467649000299) ^ 21495378428614 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 150467649000299) ^ 373727746 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 150467649000299) ^ 5636582 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_150957953341903 : Nat.Prime 150957953341903 := by
  apply lucas_primality 150957953341903 (3 : ZMod 150957953341903)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (41, 1), (18169, 1), (229759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (41, 1), (18169, 1), (229759, 1)] : List FactorBlock).map factorBlockValue).prod) = 150957953341903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_18169
      · exact prime_ninetyTwoCL_229759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150957953341903) ^ 75478976670951 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150957953341903) ^ 50319317780634 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150957953341903) ^ 21565421905986 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150957953341903) ^ 3681901301022 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150957953341903) ^ 8308544958 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150957953341903) ^ 657027378 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_203319708809621 : Nat.Prime 203319708809621 := by
  apply lucas_primality 203319708809621 (2 : ZMod 203319708809621)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (781998880037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (781998880037, 1)] : List FactorBlock).map factorBlockValue).prod) = 203319708809621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_781998880037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 203319708809621) ^ 101659854404810 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 203319708809621) ^ 40663941761924 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 203319708809621) ^ 15639977600740 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 203319708809621) ^ 260 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_230424409790173 : Nat.Prime 230424409790173 := by
  apply lucas_primality 230424409790173 (2 : ZMod 230424409790173)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (1061, 1), (10223, 1), (15131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (1061, 1), (10223, 1), (15131, 1)] : List FactorBlock).map factorBlockValue).prod) = 230424409790173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_1061
      · exact prime_ninetyTwoCL_10223
      · exact prime_ninetyTwoCL_15131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230424409790173) ^ 115212204895086 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 230424409790173) ^ 76808136596724 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 230424409790173) ^ 17724954599244 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 230424409790173) ^ 217176635052 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 230424409790173) ^ 22539803364 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 230424409790173) ^ 15228630612 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_433850767404289 : Nat.Prime 433850767404289 := by
  apply lucas_primality 433850767404289 (23 : ZMod 433850767404289)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (47189, 1), (920863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (47189, 1), (920863, 1)] : List FactorBlock).map factorBlockValue).prod) = 433850767404289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_47189
      · exact prime_ninetyTwoCL_920863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 433850767404289) ^ 216925383702144 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (23 : ZMod 433850767404289) ^ 144616922468096 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (23 : ZMod 433850767404289) ^ 33373135954176 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (23 : ZMod 433850767404289) ^ 9193896192 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (23 : ZMod 433850767404289) ^ 471134976 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_570284585537753 : Nat.Prime 570284585537753 := by
  apply lucas_primality 570284585537753 (3 : ZMod 570284585537753)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (289847, 1), (14467181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (289847, 1), (14467181, 1)] : List FactorBlock).map factorBlockValue).prod) = 570284585537753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_289847
      · exact prime_ninetyTwoCL_14467181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 570284585537753) ^ 285142292768876 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 570284585537753) ^ 33546152090456 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 570284585537753) ^ 1967536616 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 570284585537753) ^ 39419192 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_799907318526803 : Nat.Prime 799907318526803 := by
  apply lucas_primality 799907318526803 (2 : ZMod 799907318526803)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (487, 1), (7973398841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (487, 1), (7973398841, 1)] : List FactorBlock).map factorBlockValue).prod) = 799907318526803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_103
      · exact prime_ninetyTwoCL_487
      · exact prime_ninetyTwoCL_7973398841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 799907318526803) ^ 399953659263401 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 799907318526803) ^ 7766090471134 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 799907318526803) ^ 1642520161246 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 799907318526803) ^ 100322 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1386337433093579 : Nat.Prime 1386337433093579 := by
  apply lucas_primality 1386337433093579 (2 : ZMod 1386337433093579)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (307, 1), (14024090407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (307, 1), (14024090407, 1)] : List FactorBlock).map factorBlockValue).prod) = 1386337433093579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_307
      · exact prime_ninetyTwoCL_14024090407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1386337433093579) ^ 693168716546789 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1386337433093579) ^ 198048204727654 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1386337433093579) ^ 60275540569286 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1386337433093579) ^ 4515757111054 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1386337433093579) ^ 98854 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3275285550666971 : Nat.Prime 3275285550666971 := by
  apply lucas_primality 3275285550666971 (6 : ZMod 3275285550666971)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19157, 1), (17097069221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19157, 1), (17097069221, 1)] : List FactorBlock).map factorBlockValue).prod) = 3275285550666971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_19157
      · exact prime_ninetyTwoCL_17097069221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3275285550666971) ^ 1637642775333485 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3275285550666971) ^ 655057110133394 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3275285550666971) ^ 170970692210 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3275285550666971) ^ 191570 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3678900750778937 : Nat.Prime 3678900750778937 := by
  apply lucas_primality 3678900750778937 (3 : ZMod 3678900750778937)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (29, 1), (158429, 1), (5887711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (29, 1), (158429, 1), (5887711, 1)] : List FactorBlock).map factorBlockValue).prod) = 3678900750778937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_158429
      · exact prime_ninetyTwoCL_5887711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3678900750778937) ^ 1839450375389468 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3678900750778937) ^ 216405926516408 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3678900750778937) ^ 126858646578584 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3678900750778937) ^ 23221132184 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3678900750778937) ^ 624843976 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_5411737338958393 : Nat.Prime 5411737338958393 := by
  apply lucas_primality 5411737338958393 (5 : ZMod 5411737338958393)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (261407, 1), (66353663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (261407, 1), (66353663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5411737338958393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_261407
      · exact prime_ninetyTwoCL_66353663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5411737338958393) ^ 2705868669479196 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5411737338958393) ^ 1803912446319464 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5411737338958393) ^ 416287487612184 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5411737338958393) ^ 20702342856 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5411737338958393) ^ 81558984 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_6139369146732539 : Nat.Prime 6139369146732539 := by
  apply lucas_primality 6139369146732539 (2 : ZMod 6139369146732539)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (15425550619931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (15425550619931, 1)] : List FactorBlock).map factorBlockValue).prod) = 6139369146732539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_199
      · exact prime_ninetyTwoCL_15425550619931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6139369146732539) ^ 3069684573366269 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6139369146732539) ^ 30851101239862 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6139369146732539) ^ 398 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_10038484040221421 : Nat.Prime 10038484040221421 := by
  apply lucas_primality 10038484040221421 (2 : ZMod 10038484040221421)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (71703457430153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (71703457430153, 1)] : List FactorBlock).map factorBlockValue).prod) = 10038484040221421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_71703457430153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10038484040221421) ^ 5019242020110710 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10038484040221421) ^ 2007696808044284 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10038484040221421) ^ 1434069148603060 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10038484040221421) ^ 140 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_11119905747659081 : Nat.Prime 11119905747659081 := by
  apply lucas_primality 11119905747659081 (3 : ZMod 11119905747659081)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (12433, 1), (54377, 1), (411197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (12433, 1), (54377, 1), (411197, 1)] : List FactorBlock).map factorBlockValue).prod) = 11119905747659081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_12433
      · exact prime_ninetyTwoCL_54377
      · exact prime_ninetyTwoCL_411197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11119905747659081) ^ 5559952873829540 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11119905747659081) ^ 2223981149531816 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11119905747659081) ^ 894386370760 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11119905747659081) ^ 204496492040 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11119905747659081) ^ 27042769640 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_12456880450009673 : Nat.Prime 12456880450009673 := by
  apply lucas_primality 12456880450009673 (3 : ZMod 12456880450009673)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (6271, 1), (12763, 1), (525809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (6271, 1), (12763, 1), (525809, 1)] : List FactorBlock).map factorBlockValue).prod) = 12456880450009673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_6271
      · exact prime_ninetyTwoCL_12763
      · exact prime_ninetyTwoCL_525809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12456880450009673) ^ 6228440225004836 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12456880450009673) ^ 336672444594856 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12456880450009673) ^ 1986426479032 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12456880450009673) ^ 976015078744 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 12456880450009673) ^ 23690884808 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_12628755722633201 : Nat.Prime 12628755722633201 := by
  apply lucas_primality 12628755722633201 (6 : ZMod 12628755722633201)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (19, 1), (160453, 1), (10356169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (19, 1), (160453, 1), (10356169, 1)] : List FactorBlock).map factorBlockValue).prod) = 12628755722633201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_160453
      · exact prime_ninetyTwoCL_10356169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12628755722633201) ^ 6314377861316600 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12628755722633201) ^ 2525751144526640 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12628755722633201) ^ 664671353822800 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12628755722633201) ^ 78706884400 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12628755722633201) ^ 1219442800 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_12866606034114229 : Nat.Prime 12866606034114229 := by
  apply lucas_primality 12866606034114229 (2 : ZMod 12866606034114229)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (97474288137229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (97474288137229, 1)] : List FactorBlock).map factorBlockValue).prod) = 12866606034114229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_97474288137229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12866606034114229) ^ 6433303017057114 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866606034114229) ^ 4288868678038076 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866606034114229) ^ 1169691457646748 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866606034114229) ^ 132 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_18221732230980139 : Nat.Prime 18221732230980139 := by
  apply lucas_primality 18221732230980139 (2 : ZMod 18221732230980139)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (433850767404289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (433850767404289, 1)] : List FactorBlock).map factorBlockValue).prod) = 18221732230980139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_433850767404289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18221732230980139) ^ 9110866115490069 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 18221732230980139) ^ 6073910743660046 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 18221732230980139) ^ 2603104604425734 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 18221732230980139) ^ 42 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_55075680956440649 : Nat.Prime 55075680956440649 := by
  apply lucas_primality 55075680956440649 (13 : ZMod 55075680956440649)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (2039, 1), (7481, 1), (9210791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (2039, 1), (7481, 1), (9210791, 1)] : List FactorBlock).map factorBlockValue).prod) = 55075680956440649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_2039
      · exact prime_ninetyTwoCL_7481
      · exact prime_ninetyTwoCL_9210791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 55075680956440649) ^ 27537840478220324 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 55075680956440649) ^ 7867954422348664 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 55075680956440649) ^ 27011123568632 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 55075680956440649) ^ 7362074716808 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (13 : ZMod 55075680956440649) ^ 5979473528 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_84971139487535503 : Nat.Prime 84971139487535503 := by
  apply lucas_primality 84971139487535503 (3 : ZMod 84971139487535503)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (29, 1), (151007, 1), (63409589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (29, 1), (151007, 1), (63409589, 1)] : List FactorBlock).map factorBlockValue).prod) = 84971139487535503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_151007
      · exact prime_ninetyTwoCL_63409589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 84971139487535503) ^ 42485569743767751 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 84971139487535503) ^ 28323713162511834 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 84971139487535503) ^ 4998302322796206 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 84971139487535503) ^ 2930039292673638 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 84971139487535503) ^ 562696692786 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 84971139487535503) ^ 1340036118 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_95074878615282749 : Nat.Prime 95074878615282749 := by
  apply lucas_primality 95074878615282749 (2 : ZMod 95074878615282749)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (13, 1), (17, 1), (463, 1), (7703, 1), (615427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (13, 1), (17, 1), (463, 1), (7703, 1), (615427, 1)] : List FactorBlock).map factorBlockValue).prod) = 95074878615282749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_463
      · exact prime_ninetyTwoCL_7703
      · exact prime_ninetyTwoCL_615427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95074878615282749) ^ 47537439307641374 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 95074878615282749) ^ 13582125516468964 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 95074878615282749) ^ 7313452201175596 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 95074878615282749) ^ 5592639918546044 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 95074878615282749) ^ 205345310184196 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 95074878615282749) ^ 12342578036516 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 95074878615282749) ^ 154486037524 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_108084071030108651 : Nat.Prime 108084071030108651 := by
  apply lucas_primality 108084071030108651 (2 : ZMod 108084071030108651)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (8707, 1), (248269371839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (8707, 1), (248269371839, 1)] : List FactorBlock).map factorBlockValue).prod) = 108084071030108651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_8707
      · exact prime_ninetyTwoCL_248269371839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 108084071030108651) ^ 54042035515054325 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 108084071030108651) ^ 21616814206021730 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 108084071030108651) ^ 12413468591950 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 108084071030108651) ^ 435350 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_147736165098934417 : Nat.Prime 147736165098934417 := by
  apply lucas_primality 147736165098934417 (5 : ZMod 147736165098934417)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (59, 1), (577, 1), (5407, 1), (16720967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (59, 1), (577, 1), (5407, 1), (16720967, 1)] : List FactorBlock).map factorBlockValue).prod) = 147736165098934417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_59
      · exact prime_ninetyTwoCL_577
      · exact prime_ninetyTwoCL_5407
      · exact prime_ninetyTwoCL_16720967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 147736165098934417) ^ 73868082549467208 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 147736165098934417) ^ 49245388366311472 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 147736165098934417) ^ 2504002798287024 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 147736165098934417) ^ 256041880587408 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 147736165098934417) ^ 27323130219888 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 147736165098934417) ^ 8835384048 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_214198651052927809 : Nat.Prime 214198651052927809 := by
  apply lucas_primality 214198651052927809 (39 : ZMod 214198651052927809)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (17, 1), (18229, 1), (3600010243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (17, 1), (18229, 1), (3600010243, 1)] : List FactorBlock).map factorBlockValue).prod) = 214198651052927809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_18229
      · exact prime_ninetyTwoCL_3600010243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 214198651052927809) ^ 107099325526463904 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (39 : ZMod 214198651052927809) ^ 71399550350975936 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (39 : ZMod 214198651052927809) ^ 12599920650172224 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (39 : ZMod 214198651052927809) ^ 11750433433152 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (39 : ZMod 214198651052927809) ^ 59499456 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_285048000246345499 : Nat.Prime 285048000246345499 := by
  apply lucas_primality 285048000246345499 (2 : ZMod 285048000246345499)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4111, 1), (22571, 1), (170666081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4111, 1), (22571, 1), (170666081, 1)] : List FactorBlock).map factorBlockValue).prod) = 285048000246345499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_4111
      · exact prime_ninetyTwoCL_22571
      · exact prime_ninetyTwoCL_170666081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 285048000246345499) ^ 142524000123172749 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 285048000246345499) ^ 95016000082115166 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 285048000246345499) ^ 69337874056518 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 285048000246345499) ^ 12628948661838 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 285048000246345499) ^ 1670208858 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_462919400466142951 : Nat.Prime 462919400466142951 := by
  apply lucas_primality 462919400466142951 (11 : ZMod 462919400466142951)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (11, 1), (627667, 1), (148994723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (11, 1), (627667, 1), (148994723, 1)] : List FactorBlock).map factorBlockValue).prod) = 462919400466142951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_627667
      · exact prime_ninetyTwoCL_148994723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 462919400466142951) ^ 231459700233071475 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 462919400466142951) ^ 154306466822047650 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 462919400466142951) ^ 92583880093228590 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 462919400466142951) ^ 42083581860558450 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 462919400466142951) ^ 737523878850 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 462919400466142951) ^ 3106951650 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_521626419801013613 : Nat.Prime 521626419801013613 := by
  apply lucas_primality 521626419801013613 (2 : ZMod 521626419801013613)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (311, 1), (179819, 1), (2331866167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (311, 1), (179819, 1), (2331866167, 1)] : List FactorBlock).map factorBlockValue).prod) = 521626419801013613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_311
      · exact prime_ninetyTwoCL_179819
      · exact prime_ninetyTwoCL_2331866167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 521626419801013613) ^ 260813209900506806 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 521626419801013613) ^ 1677255369135092 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 521626419801013613) ^ 2900841511748 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 521626419801013613) ^ 223694836 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_526014454620716213 : Nat.Prime 526014454620716213 := by
  apply lucas_primality 526014454620716213 (2 : ZMod 526014454620716213)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (55219, 1), (2381492125087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (55219, 1), (2381492125087, 1)] : List FactorBlock).map factorBlockValue).prod) = 526014454620716213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_55219
      · exact prime_ninetyTwoCL_2381492125087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 526014454620716213) ^ 263007227310358106 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 526014454620716213) ^ 9525968500348 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 526014454620716213) ^ 220876 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_808253039603458249 : Nat.Prime 808253039603458249 := by
  apply lucas_primality 808253039603458249 (7 : ZMod 808253039603458249)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (32363, 1), (1040608410329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (32363, 1), (1040608410329, 1)] : List FactorBlock).map factorBlockValue).prod) = 808253039603458249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_32363
      · exact prime_ninetyTwoCL_1040608410329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 808253039603458249) ^ 404126519801729124 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 808253039603458249) ^ 269417679867819416 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 808253039603458249) ^ 24974601847896 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 808253039603458249) ^ 776712 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1477361650989344171 : Nat.Prime 1477361650989344171 := by
  apply lucas_primality 1477361650989344171 (2 : ZMod 1477361650989344171)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (147736165098934417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (147736165098934417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477361650989344171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_147736165098934417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1477361650989344171) ^ 738680825494672085 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1477361650989344171) ^ 295472330197868834 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1477361650989344171) ^ 10 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1589153938605689513 : Nat.Prime 1589153938605689513 := by
  apply lucas_primality 1589153938605689513 (3 : ZMod 1589153938605689513)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (342847, 1), (82770882941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (342847, 1), (82770882941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1589153938605689513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_342847
      · exact prime_ninetyTwoCL_82770882941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1589153938605689513) ^ 794576969302844756 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1589153938605689513) ^ 227021991229384216 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1589153938605689513) ^ 4635169444696 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1589153938605689513) ^ 19199432 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1735059104280005521 : Nat.Prime 1735059104280005521 := by
  apply lucas_primality 1735059104280005521 (11 : ZMod 1735059104280005521)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (23, 1), (41, 1), (89, 1), (8783, 1), (9807503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (23, 1), (41, 1), (89, 1), (8783, 1), (9807503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1735059104280005521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_89
      · exact prime_ninetyTwoCL_8783
      · exact prime_ninetyTwoCL_9807503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1735059104280005521) ^ 867529552140002760 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1735059104280005521) ^ 578353034760001840 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1735059104280005521) ^ 347011820856001104 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1735059104280005521) ^ 75437352360000240 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1735059104280005521) ^ 42318514738536720 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1735059104280005521) ^ 19495046115505680 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1735059104280005521) ^ 197547433027440 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1735059104280005521) ^ 176911401840 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1761952152433926851 : Nat.Prime 1761952152433926851 := by
  apply lucas_primality 1761952152433926851 (6 : ZMod 1761952152433926851)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (24584561, 1), (1433381017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (24584561, 1), (1433381017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1761952152433926851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_24584561
      · exact prime_ninetyTwoCL_1433381017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1761952152433926851) ^ 880976076216963425 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 1761952152433926851) ^ 352390430486785370 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 1761952152433926851) ^ 71669050850 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 1761952152433926851) ^ 1229228050 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1872909180087841439 : Nat.Prime 1872909180087841439 := by
  apply lucas_primality 1872909180087841439 (11 : ZMod 1872909180087841439)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2034257, 1), (460342321567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2034257, 1), (460342321567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1872909180087841439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_2034257
      · exact prime_ninetyTwoCL_460342321567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1872909180087841439) ^ 936454590043920719 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1872909180087841439) ^ 920684643134 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1872909180087841439) ^ 4068514 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2607369892442200247 : Nat.Prime 2607369892442200247 := by
  apply lucas_primality 2607369892442200247 (5 : ZMod 2607369892442200247)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (1927031, 1), (4867087447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (1927031, 1), (4867087447, 1)] : List FactorBlock).map factorBlockValue).prod) = 2607369892442200247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_139
      · exact prime_ninetyTwoCL_1927031
      · exact prime_ninetyTwoCL_4867087447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2607369892442200247) ^ 1303684946221100123 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2607369892442200247) ^ 18758056780159714 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2607369892442200247) ^ 1353050310266 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2607369892442200247) ^ 535714618 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2882517593862586651 : Nat.Prime 2882517593862586651 := by
  apply lucas_primality 2882517593862586651 (10 : ZMod 2882517593862586651)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (10219333, 1), (1880434267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (10219333, 1), (1880434267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2882517593862586651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_10219333
      · exact prime_ninetyTwoCL_1880434267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2882517593862586651) ^ 1441258796931293325 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 2882517593862586651) ^ 960839197954195550 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 2882517593862586651) ^ 576503518772517330 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 2882517593862586651) ^ 282065140050 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 2882517593862586651) ^ 1532899950 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3455819738612157671 : Nat.Prime 3455819738612157671 := by
  apply lucas_primality 3455819738612157671 (29 : ZMod 3455819738612157671)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (89689, 1), (296393412331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (89689, 1), (296393412331, 1)] : List FactorBlock).map factorBlockValue).prod) = 3455819738612157671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_89689
      · exact prime_ninetyTwoCL_296393412331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 3455819738612157671) ^ 1727909869306078835 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (29 : ZMod 3455819738612157671) ^ 691163947722431534 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (29 : ZMod 3455819738612157671) ^ 265832287585550590 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (29 : ZMod 3455819738612157671) ^ 38531143603030 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (29 : ZMod 3455819738612157671) ^ 11659570 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3538341026242234477 : Nat.Prime 3538341026242234477 := by
  apply lucas_primality 3538341026242234477 (6 : ZMod 3538341026242234477)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (998737, 1), (2439955649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (998737, 1), (2439955649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3538341026242234477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_998737
      · exact prime_ninetyTwoCL_2439955649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3538341026242234477) ^ 1769170513121117238 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3538341026242234477) ^ 1179447008747411492 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3538341026242234477) ^ 321667366022021316 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3538341026242234477) ^ 3542815602348 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3538341026242234477) ^ 1450166124 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3543515733802260317 : Nat.Prime 3543515733802260317 := by
  apply lucas_primality 3543515733802260317 (2 : ZMod 3543515733802260317)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (6263, 1), (6149844382471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (6263, 1), (6149844382471, 1)] : List FactorBlock).map factorBlockValue).prod) = 3543515733802260317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_6263
      · exact prime_ninetyTwoCL_6149844382471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3543515733802260317) ^ 1771757866901130158 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3543515733802260317) ^ 154065901469663492 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3543515733802260317) ^ 565785683187332 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3543515733802260317) ^ 576196 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4316983022176680731 : Nat.Prime 4316983022176680731 := by
  apply lucas_primality 4316983022176680731 (2 : ZMod 4316983022176680731)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (107, 1), (7873, 1), (35339, 1), (2071591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (107, 1), (7873, 1), (35339, 1), (2071591, 1)] : List FactorBlock).map factorBlockValue).prod) = 4316983022176680731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_107
      · exact prime_ninetyTwoCL_7873
      · exact prime_ninetyTwoCL_35339
      · exact prime_ninetyTwoCL_2071591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4316983022176680731) ^ 2158491511088340365 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316983022176680731) ^ 863396604435336146 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316983022176680731) ^ 616711860310954390 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316983022176680731) ^ 40345635721277390 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316983022176680731) ^ 548327578074010 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316983022176680731) ^ 122159173213070 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316983022176680731) ^ 2083897363030 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_5337082144922149361 : Nat.Prime 5337082144922149361 := by
  apply lucas_primality 5337082144922149361 (3 : ZMod 5337082144922149361)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (6073, 1), (10985267052779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (6073, 1), (10985267052779, 1)] : List FactorBlock).map factorBlockValue).prod) = 5337082144922149361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_6073
      · exact prime_ninetyTwoCL_10985267052779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5337082144922149361) ^ 2668541072461074680 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5337082144922149361) ^ 1067416428984429872 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5337082144922149361) ^ 878821364222320 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5337082144922149361) ^ 485840 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_6651974160305165383 : Nat.Prime 6651974160305165383 := by
  apply lucas_primality 6651974160305165383 (10 : ZMod 6651974160305165383)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (12456880450009673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (12456880450009673, 1)] : List FactorBlock).map factorBlockValue).prod) = 6651974160305165383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_89
      · exact prime_ninetyTwoCL_12456880450009673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 6651974160305165383) ^ 3325987080152582691 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 6651974160305165383) ^ 2217324720101721794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 6651974160305165383) ^ 74741282700058038 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 6651974160305165383) ^ 534 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_7662620051023693663 : Nat.Prime 7662620051023693663 := by
  apply lucas_primality 7662620051023693663 (3 : ZMod 7662620051023693663)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (3361, 1), (4367553929411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (3361, 1), (4367553929411, 1)] : List FactorBlock).map factorBlockValue).prod) = 7662620051023693663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_3361
      · exact prime_ninetyTwoCL_4367553929411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7662620051023693663) ^ 3831310025511846831 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7662620051023693663) ^ 2554206683674564554 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7662620051023693663) ^ 264228277621506678 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7662620051023693663) ^ 2279863151152542 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7662620051023693663) ^ 1754442 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_10674164289844298723 : Nat.Prime 10674164289844298723 := by
  apply lucas_primality 10674164289844298723 (2 : ZMod 10674164289844298723)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5337082144922149361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5337082144922149361, 1)] : List FactorBlock).map factorBlockValue).prod) = 10674164289844298723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5337082144922149361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10674164289844298723) ^ 5337082144922149361 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10674164289844298723) ^ 2 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_14278294202820937687 : Nat.Prime 14278294202820937687 := by
  apply lucas_primality 14278294202820937687 (3 : ZMod 14278294202820937687)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (4397, 1), (4400109646951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (4397, 1), (4400109646951, 1)] : List FactorBlock).map factorBlockValue).prod) = 14278294202820937687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_4397
      · exact prime_ninetyTwoCL_4400109646951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14278294202820937687) ^ 7139147101410468843 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14278294202820937687) ^ 4759431400940312562 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14278294202820937687) ^ 348251078117583846 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14278294202820937687) ^ 3247280919449838 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14278294202820937687) ^ 3244986 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_18670416747154563421 : Nat.Prime 18670416747154563421 := by
  apply lucas_primality 18670416747154563421 (10 : ZMod 18670416747154563421)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (449, 1), (219277, 1), (1053518303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (449, 1), (219277, 1), (1053518303, 1)] : List FactorBlock).map factorBlockValue).prod) = 18670416747154563421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_449
      · exact prime_ninetyTwoCL_219277
      · exact prime_ninetyTwoCL_1053518303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 18670416747154563421) ^ 9335208373577281710 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 18670416747154563421) ^ 6223472249051521140 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 18670416747154563421) ^ 3734083349430912684 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 18670416747154563421) ^ 41582219926847580 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 18670416747154563421) ^ 85145349248460 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (10 : ZMod 18670416747154563421) ^ 17721967140 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_26588681473406728147 : Nat.Prime 26588681473406728147 := by
  apply lucas_primality 26588681473406728147 (3 : ZMod 26588681473406728147)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (108084071030108651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (108084071030108651, 1)] : List FactorBlock).map factorBlockValue).prod) = 26588681473406728147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_41
      · exact prime_ninetyTwoCL_108084071030108651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26588681473406728147) ^ 13294340736703364073 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 26588681473406728147) ^ 8862893824468909382 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 26588681473406728147) ^ 648504426180651906 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 26588681473406728147) ^ 246 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_30074832869124310643 : Nat.Prime 30074832869124310643 := by
  apply lucas_primality 30074832869124310643 (2 : ZMod 30074832869124310643)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (401, 1), (1550771, 1), (24181385651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (401, 1), (1550771, 1), (24181385651, 1)] : List FactorBlock).map factorBlockValue).prod) = 30074832869124310643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_401
      · exact prime_ninetyTwoCL_1550771
      · exact prime_ninetyTwoCL_24181385651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30074832869124310643) ^ 15037416434562155321 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 30074832869124310643) ^ 74999583214773842 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 30074832869124310643) ^ 19393471292102 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 30074832869124310643) ^ 1243718342 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_47930280449754077953 : Nat.Prime 47930280449754077953 := by
  apply lucas_primality 47930280449754077953 (11 : ZMod 47930280449754077953)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (4363, 1), (14304198793403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (4363, 1), (14304198793403, 1)] : List FactorBlock).map factorBlockValue).prod) = 47930280449754077953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_4363
      · exact prime_ninetyTwoCL_14304198793403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 47930280449754077953) ^ 23965140224877038976 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 47930280449754077953) ^ 15976760149918025984 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 47930280449754077953) ^ 10985624673333504 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (11 : ZMod 47930280449754077953) ^ 3350784 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_56324814639148593389 : Nat.Prime 56324814639148593389 := by
  apply lucas_primality 56324814639148593389 (2 : ZMod 56324814639148593389)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (967, 1), (3823103, 1), (3808880147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (967, 1), (3823103, 1), (3808880147, 1)] : List FactorBlock).map factorBlockValue).prod) = 56324814639148593389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_967
      · exact prime_ninetyTwoCL_3823103
      · exact prime_ninetyTwoCL_3808880147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56324814639148593389) ^ 28162407319574296694 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 56324814639148593389) ^ 58246964466544564 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 56324814639148593389) ^ 14732748408596 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 56324814639148593389) ^ 14787762404 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_120221593790079227461 : Nat.Prime 120221593790079227461 := by
  apply lucas_primality 120221593790079227461 (6 : ZMod 120221593790079227461)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 3), (60333061, 1), (96823717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 3), (60333061, 1), (96823717, 1)] : List FactorBlock).map factorBlockValue).prod) = 120221593790079227461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_60333061
      · exact prime_ninetyTwoCL_96823717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 120221593790079227461) ^ 60110796895039613730 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 120221593790079227461) ^ 40073864596693075820 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 120221593790079227461) ^ 24044318758015845492 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 120221593790079227461) ^ 17174513398582746780 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 120221593790079227461) ^ 1992632095860 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 120221593790079227461) ^ 1241654395380 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_160598730984217144933 : Nat.Prime 160598730984217144933 := by
  apply lucas_primality 160598730984217144933 (2 : ZMod 160598730984217144933)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (19, 1), (479, 1), (110039, 1), (786097097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (19, 1), (479, 1), (110039, 1), (786097097, 1)] : List FactorBlock).map factorBlockValue).prod) = 160598730984217144933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_479
      · exact prime_ninetyTwoCL_110039
      · exact prime_ninetyTwoCL_786097097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160598730984217144933) ^ 80299365492108572466 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 160598730984217144933) ^ 53532910328072381644 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 160598730984217144933) ^ 9446984175542184996 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 160598730984217144933) ^ 8452564788643007628 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 160598730984217144933) ^ 335279187858490908 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 160598730984217144933) ^ 1459471014678588 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 160598730984217144933) ^ 204298847556 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_226788492838311462029 : Nat.Prime 226788492838311462029 := by
  apply lucas_primality 226788492838311462029 (2 : ZMod 226788492838311462029)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (2687, 1), (570284585537753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (2687, 1), (570284585537753, 1)] : List FactorBlock).map factorBlockValue).prod) = 226788492838311462029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_37
      · exact prime_ninetyTwoCL_2687
      · exact prime_ninetyTwoCL_570284585537753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 226788492838311462029) ^ 113394246419155731014 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 226788492838311462029) ^ 6129418725359769244 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 226788492838311462029) ^ 84402118659587444 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 226788492838311462029) ^ 397676 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_266078966412206615321 : Nat.Prime 266078966412206615321 := by
  apply lucas_primality 266078966412206615321 (3 : ZMod 266078966412206615321)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (6651974160305165383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (6651974160305165383, 1)] : List FactorBlock).map factorBlockValue).prod) = 266078966412206615321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_6651974160305165383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 266078966412206615321) ^ 133039483206103307660 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 266078966412206615321) ^ 53215793282441323064 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 266078966412206615321) ^ 40 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_311638982428429492327 : Nat.Prime 311638982428429492327 := by
  apply lucas_primality 311638982428429492327 (5 : ZMod 311638982428429492327)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (73, 1), (1201, 1), (3679669251257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (73, 1), (1201, 1), (3679669251257, 1)] : List FactorBlock).map factorBlockValue).prod) = 311638982428429492327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_73
      · exact prime_ninetyTwoCL_1201
      · exact prime_ninetyTwoCL_3679669251257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 311638982428429492327) ^ 155819491214214746163 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 311638982428429492327) ^ 103879660809476497442 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 311638982428429492327) ^ 44519854632632784618 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 311638982428429492327) ^ 13549520975149108362 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 311638982428429492327) ^ 4269027156553828662 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 311638982428429492327) ^ 259482916260141126 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 311638982428429492327) ^ 84692118 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_503874200388258655937 : Nat.Prime 503874200388258655937 := by
  apply lucas_primality 503874200388258655937 (3 : ZMod 503874200388258655937)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (661825331, 1), (11895939929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (661825331, 1), (11895939929, 1)] : List FactorBlock).map factorBlockValue).prod) = 503874200388258655937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_661825331
      · exact prime_ninetyTwoCL_11895939929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 503874200388258655937) ^ 251937100194129327968 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 503874200388258655937) ^ 761340155456 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 503874200388258655937) ^ 42356821184 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_610670548578256800869 : Nat.Prime 610670548578256800869 := by
  apply lucas_primality 610670548578256800869 (2 : ZMod 610670548578256800869)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (43, 1), (197, 1), (1386337433093579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (43, 1), (197, 1), (1386337433093579, 1)] : List FactorBlock).map factorBlockValue).prod) = 610670548578256800869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_43
      · exact prime_ninetyTwoCL_197
      · exact prime_ninetyTwoCL_1386337433093579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 610670548578256800869) ^ 305335274289128400434 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 610670548578256800869) ^ 46974657582942830836 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 610670548578256800869) ^ 14201640664610623276 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 610670548578256800869) ^ 3099850500397242644 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 610670548578256800869) ^ 440492 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_651061529254152209023 : Nat.Prime 651061529254152209023 := by
  apply lucas_primality 651061529254152209023 (5 : ZMod 651061529254152209023)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (3613, 1), (4878217, 1), (37770619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (3613, 1), (4878217, 1), (37770619, 1)] : List FactorBlock).map factorBlockValue).prod) = 651061529254152209023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_163
      · exact prime_ninetyTwoCL_3613
      · exact prime_ninetyTwoCL_4878217
      · exact prime_ninetyTwoCL_37770619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 651061529254152209023) ^ 325530764627076104511 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 651061529254152209023) ^ 217020509751384069674 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 651061529254152209023) ^ 3994242510761669994 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 651061529254152209023) ^ 180199703640783894 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 651061529254152209023) ^ 133463011025166 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 651061529254152209023) ^ 17237248064538 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_956135329042299907021 : Nat.Prime 956135329042299907021 := by
  apply lucas_primality 956135329042299907021 (6 : ZMod 956135329042299907021)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (6029, 1), (203319708809621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (6029, 1), (203319708809621, 1)] : List FactorBlock).map factorBlockValue).prod) = 956135329042299907021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_6029
      · exact prime_ninetyTwoCL_203319708809621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 956135329042299907021) ^ 478067664521149953510 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 956135329042299907021) ^ 318711776347433302340 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 956135329042299907021) ^ 191227065808459981404 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 956135329042299907021) ^ 73548871464792300540 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 956135329042299907021) ^ 158589372871504380 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 956135329042299907021) ^ 4702620 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1123089120970601266061 : Nat.Prime 1123089120970601266061 := by
  apply lucas_primality 1123089120970601266061 (2 : ZMod 1123089120970601266061)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (197, 1), (285048000246345499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (197, 1), (285048000246345499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123089120970601266061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_197
      · exact prime_ninetyTwoCL_285048000246345499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1123089120970601266061) ^ 561544560485300633030 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123089120970601266061) ^ 224617824194120253212 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123089120970601266061) ^ 5700960004926909980 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123089120970601266061) ^ 3940 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1503741643456215532151 : Nat.Prime 1503741643456215532151 := by
  apply lucas_primality 1503741643456215532151 (23 : ZMod 1503741643456215532151)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (30074832869124310643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (30074832869124310643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1503741643456215532151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_30074832869124310643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 1503741643456215532151) ^ 751870821728107766075 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (23 : ZMod 1503741643456215532151) ^ 300748328691243106430 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (23 : ZMod 1503741643456215532151) ^ 50 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2489134426430983245457 : Nat.Prime 2489134426430983245457 := by
  apply lucas_primality 2489134426430983245457 (5 : ZMod 2489134426430983245457)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (547, 1), (6871, 1), (12109, 1), (1139440259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (547, 1), (6871, 1), (12109, 1), (1139440259, 1)] : List FactorBlock).map factorBlockValue).prod) = 2489134426430983245457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_547
      · exact prime_ninetyTwoCL_6871
      · exact prime_ninetyTwoCL_12109
      · exact prime_ninetyTwoCL_1139440259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2489134426430983245457) ^ 1244567213215491622728 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2489134426430983245457) ^ 829711475476994415152 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2489134426430983245457) ^ 4550519975193753648 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2489134426430983245457) ^ 362266689918641136 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2489134426430983245457) ^ 205560692578328784 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2489134426430983245457) ^ 2184523854384 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2701595177864410442743 : Nat.Prime 2701595177864410442743 := by
  apply lucas_primality 2701595177864410442743 (5 : ZMod 2701595177864410442743)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (47, 1), (1117, 1), (150467649000299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (47, 1), (1117, 1), (150467649000299, 1)] : List FactorBlock).map factorBlockValue).prod) = 2701595177864410442743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_47
      · exact prime_ninetyTwoCL_1117
      · exact prime_ninetyTwoCL_150467649000299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2701595177864410442743) ^ 1350797588932205221371 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2701595177864410442743) ^ 900531725954803480914 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2701595177864410442743) ^ 142189219887600549618 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2701595177864410442743) ^ 57480748465200222186 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2701595177864410442743) ^ 2418616990030806126 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2701595177864410442743) ^ 17954658 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_7054238805435621183119 : Nat.Prime 7054238805435621183119 := by
  apply lucas_primality 7054238805435621183119 (7 : ZMod 7054238805435621183119)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (503874200388258655937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (503874200388258655937, 1)] : List FactorBlock).map factorBlockValue).prod) = 7054238805435621183119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_503874200388258655937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 7054238805435621183119) ^ 3527119402717810591559 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 7054238805435621183119) ^ 1007748400776517311874 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 7054238805435621183119) ^ 14 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_8737755037668335681029 : Nat.Prime 8737755037668335681029 := by
  apply lucas_primality 8737755037668335681029 (2 : ZMod 8737755037668335681029)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (18670416747154563421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (18670416747154563421, 1)] : List FactorBlock).map factorBlockValue).prod) = 8737755037668335681029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_18670416747154563421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8737755037668335681029) ^ 4368877518834167840514 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8737755037668335681029) ^ 2912585012556111893676 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8737755037668335681029) ^ 672135002897564283156 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8737755037668335681029) ^ 468 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_11026644581737665105193 : Nat.Prime 11026644581737665105193 := by
  apply lucas_primality 11026644581737665105193 (5 : ZMod 11026644581737665105193)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (17, 1), (53, 1), (1209707, 1), (12773596993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (17, 1), (53, 1), (1209707, 1), (12773596993, 1)] : List FactorBlock).map factorBlockValue).prod) = 11026644581737665105193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_53
      · exact prime_ninetyTwoCL_1209707
      · exact prime_ninetyTwoCL_12773596993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11026644581737665105193) ^ 5513322290868832552596 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11026644581737665105193) ^ 3675548193912555035064 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11026644581737665105193) ^ 1002422234703424100472 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11026644581737665105193) ^ 648626151866921476776 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11026644581737665105193) ^ 208049897768635190664 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11026644581737665105193) ^ 9115136625428856 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11026644581737665105193) ^ 863237237544 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_14655704049399105637279 : Nat.Prime 14655704049399105637279 := by
  apply lucas_primality 14655704049399105637279 (3 : ZMod 14655704049399105637279)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (653, 1), (76260971, 1), (590965097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (653, 1), (76260971, 1), (590965097, 1)] : List FactorBlock).map factorBlockValue).prod) = 14655704049399105637279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_83
      · exact prime_ninetyTwoCL_653
      · exact prime_ninetyTwoCL_76260971
      · exact prime_ninetyTwoCL_590965097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14655704049399105637279) ^ 7327852024699552818639 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14655704049399105637279) ^ 4885234683133035212426 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14655704049399105637279) ^ 176574747583121754666 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14655704049399105637279) ^ 22443650917915935126 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14655704049399105637279) ^ 192178303753818 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14655704049399105637279) ^ 24799610203374 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_14934806558585899472743 : Nat.Prime 14934806558585899472743 := by
  apply lucas_primality 14934806558585899472743 (3 : ZMod 14934806558585899472743)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2489134426430983245457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2489134426430983245457, 1)] : List FactorBlock).map factorBlockValue).prod) = 14934806558585899472743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_2489134426430983245457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14934806558585899472743) ^ 7467403279292949736371 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14934806558585899472743) ^ 4978268852861966490914 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14934806558585899472743) ^ 6 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_17154683989304820158267 : Nat.Prime 17154683989304820158267 := by
  apply lucas_primality 17154683989304820158267 (2 : ZMod 17154683989304820158267)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (109, 1), (47389, 1), (150957953341903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (109, 1), (47389, 1), (150957953341903, 1)] : List FactorBlock).map factorBlockValue).prod) = 17154683989304820158267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_109
      · exact prime_ninetyTwoCL_47389
      · exact prime_ninetyTwoCL_150957953341903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17154683989304820158267) ^ 8577341994652410079133 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17154683989304820158267) ^ 1559516726300438196206 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17154683989304820158267) ^ 157382421920227707874 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17154683989304820158267) ^ 361997172113883394 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17154683989304820158267) ^ 113638822 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_50209831294874005858451 : Nat.Prime 50209831294874005858451 := by
  apply lucas_primality 50209831294874005858451 (2 : ZMod 50209831294874005858451)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (113, 1), (5849, 1), (6277, 1), (242050823381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (113, 1), (5849, 1), (6277, 1), (242050823381, 1)] : List FactorBlock).map factorBlockValue).prod) = 50209831294874005858451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_113
      · exact prime_ninetyTwoCL_5849
      · exact prime_ninetyTwoCL_6277
      · exact prime_ninetyTwoCL_242050823381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50209831294874005858451) ^ 25104915647437002929225 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50209831294874005858451) ^ 10041966258974801171690 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50209831294874005858451) ^ 444334790220123945650 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50209831294874005858451) ^ 8584344553748334050 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50209831294874005858451) ^ 7999017252648399850 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50209831294874005858451) ^ 207435077450 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_64513242880411759402229 : Nat.Prime 64513242880411759402229 := by
  apply lucas_primality 64513242880411759402229 (2 : ZMod 64513242880411759402229)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (359, 1), (3455819738612157671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (359, 1), (3455819738612157671, 1)] : List FactorBlock).map factorBlockValue).prod) = 64513242880411759402229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_359
      · exact prime_ninetyTwoCL_3455819738612157671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64513242880411759402229) ^ 32256621440205879701114 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 64513242880411759402229) ^ 4962557144647058415556 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 64513242880411759402229) ^ 179702626407832198892 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 64513242880411759402229) ^ 18668 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_87074471267891981557807 : Nat.Prime 87074471267891981557807 := by
  apply lucas_primality 87074471267891981557807 (5 : ZMod 87074471267891981557807)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (277, 1), (131899, 1), (1224029, 1), (19088759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (277, 1), (131899, 1), (1224029, 1), (19088759, 1)] : List FactorBlock).map factorBlockValue).prod) = 87074471267891981557807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_17
      · exact prime_ninetyTwoCL_277
      · exact prime_ninetyTwoCL_131899
      · exact prime_ninetyTwoCL_1224029
      · exact prime_ninetyTwoCL_19088759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 87074471267891981557807) ^ 43537235633945990778903 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 87074471267891981557807) ^ 29024823755963993852602 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 87074471267891981557807) ^ 5122027721640704797518 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 87074471267891981557807) ^ 314348271725241810678 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 87074471267891981557807) ^ 660160207946170794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 87074471267891981557807) ^ 71137588462276614 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 87074471267891981557807) ^ 4561557473060034 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_274114297725452775733481 : Nat.Prime 274114297725452775733481 := by
  apply lucas_primality 274114297725452775733481 (3 : ZMod 274114297725452775733481)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (23, 1), (107, 1), (214198651052927809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (23, 1), (107, 1), (214198651052927809, 1)] : List FactorBlock).map factorBlockValue).prod) = 274114297725452775733481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_107
      · exact prime_ninetyTwoCL_214198651052927809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 274114297725452775733481) ^ 137057148862726387866740 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 274114297725452775733481) ^ 54822859545090555146696 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 274114297725452775733481) ^ 21085715209650213517960 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 274114297725452775733481) ^ 11918012944584903292760 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 274114297725452775733481) ^ 2561815866593016595640 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 274114297725452775733481) ^ 1279720 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_635590214091390530070971 : Nat.Prime 635590214091390530070971 := by
  apply lucas_primality 635590214091390530070971 (2 : ZMod 635590214091390530070971)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1168068001, 1), (54413802411097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1168068001, 1), (54413802411097, 1)] : List FactorBlock).map factorBlockValue).prod) = 635590214091390530070971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_1168068001
      · exact prime_ninetyTwoCL_54413802411097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 635590214091390530070971) ^ 317795107045695265035485 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 635590214091390530070971) ^ 127118042818278106014194 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 635590214091390530070971) ^ 544138024110970 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 635590214091390530070971) ^ 11680680010 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1040688060559719673648487 : Nat.Prime 1040688060559719673648487 := by
  apply lucas_primality 1040688060559719673648487 (5 : ZMod 1040688060559719673648487)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (643, 1), (941, 1), (50329, 1), (88534873213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (643, 1), (941, 1), (50329, 1), (88534873213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1040688060559719673648487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_193
      · exact prime_ninetyTwoCL_643
      · exact prime_ninetyTwoCL_941
      · exact prime_ninetyTwoCL_50329
      · exact prime_ninetyTwoCL_88534873213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1040688060559719673648487) ^ 520344030279859836824243 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040688060559719673648487) ^ 5392166116889739241702 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040688060559719673648487) ^ 1618488430108428730402 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040688060559719673648487) ^ 1105938427799914637246 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040688060559719673648487) ^ 20677701932478683734 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040688060559719673648487) ^ 11754555270622 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3113009540282188363223963 : Nat.Prime 3113009540282188363223963 := by
  apply lucas_primality 3113009540282188363223963 (2 : ZMod 3113009540282188363223963)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (50209831294874005858451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (50209831294874005858451, 1)] : List FactorBlock).map factorBlockValue).prod) = 3113009540282188363223963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_31
      · exact prime_ninetyTwoCL_50209831294874005858451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3113009540282188363223963) ^ 1556504770141094181611981 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3113009540282188363223963) ^ 100419662589748011716902 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3113009540282188363223963) ^ 62 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_4401981194603572034928377 : Nat.Prime 4401981194603572034928377 := by
  apply lucas_primality 4401981194603572034928377 (3 : ZMod 4401981194603572034928377)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (269, 1), (397, 1), (52976207, 1), (3353795293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (269, 1), (397, 1), (52976207, 1), (3353795293, 1)] : List FactorBlock).map factorBlockValue).prod) = 4401981194603572034928377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_29
      · exact prime_ninetyTwoCL_269
      · exact prime_ninetyTwoCL_397
      · exact prime_ninetyTwoCL_52976207
      · exact prime_ninetyTwoCL_3353795293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4401981194603572034928377) ^ 2200990597301786017464188 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401981194603572034928377) ^ 151792454986330070169944 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401981194603572034928377) ^ 16364242359121085631704 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401981194603572034928377) ^ 11088113840311264571608 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401981194603572034928377) ^ 83093551688280968 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4401981194603572034928377) ^ 1312537233203032 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_11925068889097649535253291 : Nat.Prime 11925068889097649535253291 := by
  apply lucas_primality 11925068889097649535253291 (3 : ZMod 11925068889097649535253291)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (1038797, 1), (18221732230980139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (1038797, 1), (18221732230980139, 1)] : List FactorBlock).map factorBlockValue).prod) = 11925068889097649535253291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_1038797
      · exact prime_ninetyTwoCL_18221732230980139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11925068889097649535253291) ^ 5962534444548824767626645 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11925068889097649535253291) ^ 3975022963032549845084430 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11925068889097649535253291) ^ 2385013777819529907050658 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11925068889097649535253291) ^ 1703581269871092790750470 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11925068889097649535253291) ^ 11479691305517487570 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11925068889097649535253291) ^ 654442110 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_16995086458978072095475823 : Nat.Prime 16995086458978072095475823 := by
  apply lucas_primality 16995086458978072095475823 (5 : ZMod 16995086458978072095475823)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (274114297725452775733481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (274114297725452775733481, 1)] : List FactorBlock).map factorBlockValue).prod) = 16995086458978072095475823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_31
      · exact prime_ninetyTwoCL_274114297725452775733481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16995086458978072095475823) ^ 8497543229489036047737911 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 16995086458978072095475823) ^ 548228595450905551466962 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 16995086458978072095475823) ^ 62 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_17683068336442799774190419 : Nat.Prime 17683068336442799774190419 := by
  apply lucas_primality 17683068336442799774190419 (6 : ZMod 17683068336442799774190419)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (101, 1), (1151593, 1), (143698279199197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (101, 1), (1151593, 1), (143698279199197, 1)] : List FactorBlock).map factorBlockValue).prod) = 17683068336442799774190419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_101
      · exact prime_ninetyTwoCL_1151593
      · exact prime_ninetyTwoCL_143698279199197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17683068336442799774190419) ^ 8841534168221399887095209 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17683068336442799774190419) ^ 768829058106208685834366 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17683068336442799774190419) ^ 175079884519235641328618 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17683068336442799774190419) ^ 15355310718667793026 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17683068336442799774190419) ^ 123056924794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_19815732070952753035351661 : Nat.Prime 19815732070952753035351661 := by
  apply lucas_primality 19815732070952753035351661 (2 : ZMod 19815732070952753035351661)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (92821, 1), (10674164289844298723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (92821, 1), (10674164289844298723, 1)] : List FactorBlock).map factorBlockValue).prod) = 19815732070952753035351661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_5
      · exact prime_ninetyTwoCL_92821
      · exact prime_ninetyTwoCL_10674164289844298723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19815732070952753035351661) ^ 9907866035476376517675830 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19815732070952753035351661) ^ 3963146414190550607070332 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19815732070952753035351661) ^ 213483285796885974460 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19815732070952753035351661) ^ 1856420 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_25448889409794024663323647 : Nat.Prime 25448889409794024663323647 := by
  apply lucas_primality 25448889409794024663323647 (3 : ZMod 25448889409794024663323647)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (347, 1), (2521, 1), (10038484040221421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (347, 1), (2521, 1), (10038484040221421, 1)] : List FactorBlock).map factorBlockValue).prod) = 25448889409794024663323647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_347
      · exact prime_ninetyTwoCL_2521
      · exact prime_ninetyTwoCL_10038484040221421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25448889409794024663323647) ^ 12724444704897012331661823 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 25448889409794024663323647) ^ 8482963136598008221107882 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 25448889409794024663323647) ^ 3635555629970574951903378 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 25448889409794024663323647) ^ 1106473452599740202753202 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 25448889409794024663323647) ^ 73339738933123990384218 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 25448889409794024663323647) ^ 10094759781750902286126 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 25448889409794024663323647) ^ 2535132726 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_57610462572807024052460417 : Nat.Prime 57610462572807024052460417 := by
  apply lucas_primality 57610462572807024052460417 (3 : ZMod 57610462572807024052460417)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (19, 1), (7232503, 1), (3275285550666971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (19, 1), (7232503, 1), (3275285550666971, 1)] : List FactorBlock).map factorBlockValue).prod) = 57610462572807024052460417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_19
      · exact prime_ninetyTwoCL_7232503
      · exact prime_ninetyTwoCL_3275285550666971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57610462572807024052460417) ^ 28805231286403512026230208 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 57610462572807024052460417) ^ 3032129609095106529076864 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 57610462572807024052460417) ^ 7965494459222073472 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 57610462572807024052460417) ^ 17589447296 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_115588260719935878226403047 : Nat.Prime 115588260719935878226403047 := by
  apply lucas_primality 115588260719935878226403047 (3 : ZMod 115588260719935878226403047)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1123, 1), (17154683989304820158267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1123, 1), (17154683989304820158267, 1)] : List FactorBlock).map factorBlockValue).prod) = 115588260719935878226403047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_1123
      · exact prime_ninetyTwoCL_17154683989304820158267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115588260719935878226403047) ^ 57794130359967939113201523 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 115588260719935878226403047) ^ 38529420239978626075467682 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 115588260719935878226403047) ^ 102928103935828920949602 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 115588260719935878226403047) ^ 6738 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_132000671526043278411462703 : Nat.Prime 132000671526043278411462703 := by
  apply lucas_primality 132000671526043278411462703 (3 : ZMod 132000671526043278411462703)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (67, 1), (6113, 1), (479317, 1), (1455399207503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (67, 1), (6113, 1), (479317, 1), (1455399207503, 1)] : List FactorBlock).map factorBlockValue).prod) = 132000671526043278411462703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_11
      · exact prime_ninetyTwoCL_67
      · exact prime_ninetyTwoCL_6113
      · exact prime_ninetyTwoCL_479317
      · exact prime_ninetyTwoCL_1455399207503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 132000671526043278411462703) ^ 66000335763021639205731351 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 132000671526043278411462703) ^ 44000223842014426137154234 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 132000671526043278411462703) ^ 18857238789434754058780386 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 132000671526043278411462703) ^ 12000061047822116219223882 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 132000671526043278411462703) ^ 1970159276508108633006906 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 132000671526043278411462703) ^ 21593435551454814070254 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 132000671526043278411462703) ^ 275393260673089580406 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 132000671526043278411462703) ^ 90697226469234 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_215810621701308852006042197 : Nat.Prime 215810621701308852006042197 := by
  apply lucas_primality 215810621701308852006042197 (2 : ZMod 215810621701308852006042197)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18717199, 1), (2882517593862586651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18717199, 1), (2882517593862586651, 1)] : List FactorBlock).map factorBlockValue).prod) = 215810621701308852006042197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_18717199
      · exact prime_ninetyTwoCL_2882517593862586651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215810621701308852006042197) ^ 107905310850654426003021098 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 215810621701308852006042197) ^ 11530070375450346604 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 215810621701308852006042197) ^ 74868796 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_788177922735214937761197589 : Nat.Prime 788177922735214937761197589 := by
  apply lucas_primality 788177922735214937761197589 (2 : ZMod 788177922735214937761197589)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (16477, 1), (4630603, 1), (95649965981281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (16477, 1), (4630603, 1), (95649965981281, 1)] : List FactorBlock).map factorBlockValue).prod) = 788177922735214937761197589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_16477
      · exact prime_ninetyTwoCL_4630603
      · exact prime_ninetyTwoCL_95649965981281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 788177922735214937761197589) ^ 394088961367607468880598794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 788177922735214937761197589) ^ 262725974245071645920399196 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 788177922735214937761197589) ^ 47835038097664316183844 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 788177922735214937761197589) ^ 170210644863145239996 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 788177922735214937761197589) ^ 8240232128148 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1157112269547443206500481567 : Nat.Prime 1157112269547443206500481567 := by
  apply lucas_primality 1157112269547443206500481567 (3 : ZMod 1157112269547443206500481567)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (2440066399, 1), (230424409790173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (2440066399, 1), (230424409790173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157112269547443206500481567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_2440066399
      · exact prime_ninetyTwoCL_230424409790173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1157112269547443206500481567) ^ 578556134773721603250240783 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157112269547443206500481567) ^ 385704089849147735500160522 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157112269547443206500481567) ^ 165301752792491886642925938 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157112269547443206500481567) ^ 474213435348176034 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1157112269547443206500481567) ^ 5021656649142 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_1182266884102822406641796383 : Nat.Prime 1182266884102822406641796383 := by
  apply lucas_primality 1182266884102822406641796383 (5 : ZMod 1182266884102822406641796383)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (16477, 1), (4630603, 1), (95649965981281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (16477, 1), (4630603, 1), (95649965981281, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822406641796383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_16477
      · exact prime_ninetyTwoCL_4630603
      · exact prime_ninetyTwoCL_95649965981281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1182266884102822406641796383) ^ 591133442051411203320898191 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1182266884102822406641796383) ^ 394088961367607468880598794 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1182266884102822406641796383) ^ 71752557146496474275766 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1182266884102822406641796383) ^ 255315967294717859994 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1182266884102822406641796383) ^ 12360348192222 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_2219766394642033906347862597 : Nat.Prime 2219766394642033906347862597 := by
  apply lucas_primality 2219766394642033906347862597 (6 : ZMod 2219766394642033906347862597)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (47, 1), (2440066399, 1), (230424409790173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (47, 1), (2440066399, 1), (230424409790173, 1)] : List FactorBlock).map factorBlockValue).prod) = 2219766394642033906347862597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_47
      · exact prime_ninetyTwoCL_2440066399
      · exact prime_ninetyTwoCL_230424409790173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2219766394642033906347862597) ^ 1109883197321016953173931298 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2219766394642033906347862597) ^ 739922131547344635449287532 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2219766394642033906347862597) ^ 317109484948861986621123228 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2219766394642033906347862597) ^ 47229072226426253326550268 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2219766394642033906347862597) ^ 909715569851603004 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2219766394642033906347862597) ^ 9633382143252 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_3750639770257229703829147147 : Nat.Prime 3750639770257229703829147147 := by
  apply lucas_primality 3750639770257229703829147147 (5 : ZMod 3750639770257229703829147147)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (211, 1), (2857, 1), (26588681473406728147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (211, 1), (2857, 1), (26588681473406728147, 1)] : List FactorBlock).map factorBlockValue).prod) = 3750639770257229703829147147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_211
      · exact prime_ninetyTwoCL_2857
      · exact prime_ninetyTwoCL_26588681473406728147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3750639770257229703829147147) ^ 1875319885128614851914573573 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3750639770257229703829147147) ^ 1250213256752409901276382382 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3750639770257229703829147147) ^ 288510751558248438756088242 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3750639770257229703829147147) ^ 17775543934868387221939086 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3750639770257229703829147147) ^ 1312789559067983795529978 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3750639770257229703829147147) ^ 141061518 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_10876855333745966141104526729 : Nat.Prime 10876855333745966141104526729 := by
  apply lucas_primality 10876855333745966141104526729 (3 : ZMod 10876855333745966141104526729)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (811, 1), (117413, 1), (14278294202820937687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (811, 1), (117413, 1), (14278294202820937687, 1)] : List FactorBlock).map factorBlockValue).prod) = 10876855333745966141104526729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_811
      · exact prime_ninetyTwoCL_117413
      · exact prime_ninetyTwoCL_14278294202820937687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10876855333745966141104526729) ^ 5438427666872983070552263364 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10876855333745966141104526729) ^ 13411658857886518053149848 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10876855333745966141104526729) ^ 92637572787902243713256 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10876855333745966141104526729) ^ 761775544 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_18128092222909943568507544549 : Nat.Prime 18128092222909943568507544549 := by
  apply lucas_primality 18128092222909943568507544549 (2 : ZMod 18128092222909943568507544549)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (215810621701308852006042197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (215810621701308852006042197, 1)] : List FactorBlock).map factorBlockValue).prod) = 18128092222909943568507544549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_7
      · exact prime_ninetyTwoCL_215810621701308852006042197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18128092222909943568507544549) ^ 9064046111454971784253772274 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 18128092222909943568507544549) ^ 6042697407636647856169181516 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 18128092222909943568507544549) ^ 2589727460415706224072506364 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 18128092222909943568507544549) ^ 84 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_27192138334364915352761316803 : Nat.Prime 27192138334364915352761316803 := by
  apply lucas_primality 27192138334364915352761316803 (2 : ZMod 27192138334364915352761316803)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (12011, 1), (87074471267891981557807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (12011, 1), (87074471267891981557807, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364915352761316803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_13
      · exact prime_ninetyTwoCL_12011
      · exact prime_ninetyTwoCL_87074471267891981557807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27192138334364915352761316803) ^ 13596069167182457676380658401 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915352761316803) ^ 2091702948797301180981639754 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915352761316803) ^ 2263936252965191520502982 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915352761316803) ^ 312286 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_36256184445819887137015089077 : Nat.Prime 36256184445819887137015089077 := by
  apply lucas_primality 36256184445819887137015089077 (2 : ZMod 36256184445819887137015089077)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (189108973, 1), (47930280449754077953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (189108973, 1), (47930280449754077953, 1)] : List FactorBlock).map factorBlockValue).prod) = 36256184445819887137015089077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_189108973
      · exact prime_ninetyTwoCL_47930280449754077953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36256184445819887137015089077) ^ 18128092222909943568507544538 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36256184445819887137015089077) ^ 191721121799016311812 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36256184445819887137015089077) ^ 756435892 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_54384276668729830705522633619 : Nat.Prime 54384276668729830705522633619 := by
  apply lucas_primality 54384276668729830705522633619 (2 : ZMod 54384276668729830705522633619)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1182266884102822406641796383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1182266884102822406641796383, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729830705522633619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_23
      · exact prime_ninetyTwoCL_1182266884102822406641796383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54384276668729830705522633619) ^ 27192138334364915352761316809 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54384276668729830705522633619) ^ 2364533768205644813283592766 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54384276668729830705522633619) ^ 46 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_54384276668729830705522633633 : Nat.Prime 54384276668729830705522633633 := by
  apply lucas_primality 54384276668729830705522633633 (7 : ZMod 54384276668729830705522633633)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (4937, 1), (298427, 1), (2788939, 1), (137867489647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (4937, 1), (298427, 1), (2788939, 1), (137867489647, 1)] : List FactorBlock).map factorBlockValue).prod) = 54384276668729830705522633633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_3
      · exact prime_ninetyTwoCL_4937
      · exact prime_ninetyTwoCL_298427
      · exact prime_ninetyTwoCL_2788939
      · exact prime_ninetyTwoCL_137867489647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 54384276668729830705522633633) ^ 27192138334364915352761316816 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 54384276668729830705522633633) ^ 18128092222909943568507544544 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 54384276668729830705522633633) ^ 11015652555950948087000736 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 54384276668729830705522633633) ^ 182236448674985275144416 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 54384276668729830705522633633) ^ 19499987869483639013088 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (7 : ZMod 54384276668729830705522633633) ^ 394467737158172256 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem prime_ninetyTwoCL_108768553337459661411045267257 : Nat.Prime 108768553337459661411045267257 := by
  apply lucas_primality 108768553337459661411045267257 (3 : ZMod 108768553337459661411045267257)
  · rw [← ninetyTwoCLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1993, 1), (308093, 1), (211793063, 1), (104547223661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1993, 1), (308093, 1), (211793063, 1), (104547223661, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyTwoCL_2
      · exact prime_ninetyTwoCL_1993
      · exact prime_ninetyTwoCL_308093
      · exact prime_ninetyTwoCL_211793063
      · exact prime_ninetyTwoCL_104547223661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 108768553337459661411045267257) ^ 54384276668729830705522633628 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 108768553337459661411045267257) ^ 54575290184375143708502392 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 108768553337459661411045267257) ^ 353038054540218899523992 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 108768553337459661411045267257) ^ 513560509474569813512 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide
    · change (3 : ZMod 108768553337459661411045267257) ^ 1040377252772847896 ≠ 1
      rw [← ninetyTwoCLFastPow_eq_pow]
      decide

private theorem phi_ninetyTwoCL_108768553337459661411045267200 : Nat.totient 108768553337459661411045267200 = 43507421334983864564418104320 := by
  rw [← show ((([(2, 8), (5, 2), (16995086458978072095475823, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_5, prime_ninetyTwoCL_16995086458978072095475823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267201 : Nat.totient 108768553337459661411045267201 = 72360225128585587004167673856 := by
  rw [← show ((([(3, 1), (569, 1), (5783, 1), (5939, 1), (26834567, 1), (69136712017, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_569, prime_ninetyTwoCL_5783, prime_ninetyTwoCL_5939, prime_ninetyTwoCL_26834567, prime_ninetyTwoCL_69136712017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267202 : Nat.totient 108768553337459661411045267202 = 52864219281948894013216783104 := by
  rw [← show ((([(2, 1), (37, 1), (1063, 1), (122819, 1), (16258933, 1), (692437802773, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_37, prime_ninetyTwoCL_1063, prime_ninetyTwoCL_122819, prime_ninetyTwoCL_16258933, prime_ninetyTwoCL_692437802773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267203 : Nat.totient 108768553337459661411045267203 = 108768553337446786351456808568 := by
  rw [← show ((([(8453554344407, 1), (12866606034114229, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_8453554344407, prime_ninetyTwoCL_12866606034114229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267204 : Nat.totient 108768553337459661411045267204 = 30415522501353336272457307776 := by
  rw [← show ((([(2, 2), (3, 1), (7, 3), (47, 1), (2440066399, 1), (230424409790173, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_7, prime_ninetyTwoCL_47, prime_ninetyTwoCL_2440066399, prime_ninetyTwoCL_230424409790173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267205 : Nat.totient 108768553337459661411045267205 = 83277689802736181315909068800 := by
  rw [← show ((([(5, 1), (29, 1), (151, 1), (463, 1), (5918085049, 1), (1812993343717, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_5, prime_ninetyTwoCL_29, prime_ninetyTwoCL_151, prime_ninetyTwoCL_463, prime_ninetyTwoCL_5918085049, prime_ninetyTwoCL_1812993343717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267206 : Nat.totient 108768553337459661411045267206 = 54384276668208204181462566760 := by
  rw [← show ((([(2, 1), (104259053231, 1), (521626419801013613, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_104259053231, prime_ninetyTwoCL_521626419801013613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267207 : Nat.totient 108768553337459661411045267207 = 61970344625929047657163822080 := by
  rw [← show ((([(3, 2), (11, 1), (17, 1), (863, 1), (143483, 1), (462830947, 1), (1127679283, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_11, prime_ninetyTwoCL_17, prime_ninetyTwoCL_863, prime_ninetyTwoCL_143483, prime_ninetyTwoCL_462830947, prime_ninetyTwoCL_1127679283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267208 : Nat.totient 108768553337459661411045267208 = 50196691196514369528444002880 := by
  rw [← show ((([(2, 3), (13, 1), (12011, 1), (87074471267891981557807, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_13, prime_ninetyTwoCL_12011, prime_ninetyTwoCL_87074471267891981557807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267209 : Nat.totient 108768553337459661411045267209 = 108768550635864483546594563604 := by
  rw [← show ((([(40260863, 1), (2701595177864410442743, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_40260863, prime_ninetyTwoCL_2701595177864410442743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267210 : Nat.totient 108768553337459661411045267210 = 28811888602787025423292059392 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (179, 1), (1019, 1), (10613, 1), (1872909180087841439, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_5, prime_ninetyTwoCL_179, prime_ninetyTwoCL_1019, prime_ninetyTwoCL_10613, prime_ninetyTwoCL_1872909180087841439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267211 : Nat.totient 108768553337459661411045267211 = 93158638161630838169398701480 := by
  rw [← show ((([(7, 1), (1303, 1), (11925068889097649535253291, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_7, prime_ninetyTwoCL_1303, prime_ninetyTwoCL_11925068889097649535253291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267212 : Nat.totient 108768553337459661411045267212 = 54384276668729830705522633604 := by
  rw [← show ((([(2, 2), (27192138334364915352761316803, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_27192138334364915352761316803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267213 : Nat.totient 108768553337459661411045267213 = 65681010052106380517283489792 := by
  rw [← show ((([(3, 1), (19, 1), (23, 1), (3347, 1), (7723, 1), (71272867, 1), (45033394529, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_19, prime_ninetyTwoCL_23, prime_ninetyTwoCL_3347, prime_ninetyTwoCL_7723, prime_ninetyTwoCL_71272867, prime_ninetyTwoCL_45033394529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267214 : Nat.totient 108768553337459661411045267214 = 53492673781450582746070255200 := by
  rw [← show ((([(2, 1), (61, 1), (932447, 1), (956135329042299907021, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_61, prime_ninetyTwoCL_932447, prime_ninetyTwoCL_956135329042299907021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267215 : Nat.totient 108768553337459661411045267215 = 84988779519362599169110416672 := by
  rw [← show ((([(5, 1), (43, 1), (34519, 1), (14655704049399105637279, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_5, prime_ninetyTwoCL_43, prime_ninetyTwoCL_34519, prime_ninetyTwoCL_14655704049399105637279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267216 : Nat.totient 108768553337459661411045267216 = 36251814678645048670856678400 := by
  rw [← show ((([(2, 4), (3, 2), (10331, 1), (42139, 1), (1735059104280005521, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_10331, prime_ninetyTwoCL_42139, prime_ninetyTwoCL_1735059104280005521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267217 : Nat.totient 108768553337459661411045267217 = 104491569934177968247581697920 := by
  rw [← show ((([(31, 1), (137, 1), (4171548949, 1), (6139369146732539, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_31, prime_ninetyTwoCL_137, prime_ninetyTwoCL_4171548949, prime_ninetyTwoCL_6139369146732539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267218 : Nat.totient 108768553337459661411045267218 = 41744025946933938526266593280 := by
  rw [← show ((([(2, 1), (7, 1), (11, 2), (97, 1), (367, 1), (509, 1), (3543515733802260317, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_7, prime_ninetyTwoCL_11, prime_ninetyTwoCL_97, prime_ninetyTwoCL_367, prime_ninetyTwoCL_509, prime_ninetyTwoCL_3543515733802260317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267219 : Nat.totient 108768553337459661411045267219 = 72512004357902593586619116160 := by
  rw [← show ((([(3, 1), (198929, 1), (3640199267, 1), (50067838215211, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_198929, prime_ninetyTwoCL_3640199267, prime_ninetyTwoCL_50067838215211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267220 : Nat.totient 108768553337459661411045267220 = 43482517258661607057512301216 := by
  rw [← show ((([(2, 2), (5, 1), (1747, 1), (3113009540282188363223963, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_5, prime_ninetyTwoCL_1747, prime_ninetyTwoCL_3113009540282188363223963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267221 : Nat.totient 108768553337459661411045267221 = 100074651828729055165966012416 := by
  rw [← show ((([(13, 1), (307, 1), (2238259, 1), (28601297, 1), (425721474097, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_13, prime_ninetyTwoCL_307, prime_ninetyTwoCL_2238259, prime_ninetyTwoCL_28601297, prime_ninetyTwoCL_425721474097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267222 : Nat.totient 108768553337459661411045267222 = 36256183913661954312465597440 := by
  rw [← show ((([(2, 1), (3, 1), (68130497, 1), (266078966412206615321, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_68130497, prime_ninetyTwoCL_266078966412206615321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267223 : Nat.totient 108768553337459661411045267223 = 108768552686398132156725994800 := by
  rw [← show ((([(167063401, 1), (651061529254152209023, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_167063401, prime_ninetyTwoCL_651061529254152209023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267224 : Nat.totient 108768553337459661411045267224 = 51185201457804314643905587200 := by
  rw [← show ((([(2, 3), (17, 1), (453910609, 1), (1761952152433926851, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_17, prime_ninetyTwoCL_453910609, prime_ninetyTwoCL_1761952152433926851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267225 : Nat.totient 108768553337459661411045267225 = 49677355554882629618739340800 := by
  rw [← show ((([(3, 4), (5, 2), (7, 1), (1103, 1), (259907, 1), (352381, 1), (75958138367, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_5, prime_ninetyTwoCL_7, prime_ninetyTwoCL_1103, prime_ninetyTwoCL_259907, prime_ninetyTwoCL_352381, prime_ninetyTwoCL_75958138367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267226 : Nat.totient 108768553337459661411045267226 = 54321310276238068791984325440 := by
  rw [← show ((([(2, 1), (1459, 1), (2269, 1), (31231, 1), (526014454620716213, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_1459, prime_ninetyTwoCL_2269, prime_ninetyTwoCL_31231, prime_ninetyTwoCL_526014454620716213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267227 : Nat.totient 108768553337459661411045267227 = 108652965076739725532818863240 := by
  rw [← show ((([(941, 1), (115588260719935878226403047, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_941, prime_ninetyTwoCL_115588260719935878226403047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267228 : Nat.totient 108768553337459661411045267228 = 36256184254098765337242341376 := by
  rw [← show ((([(2, 2), (3, 1), (189108973, 1), (47930280449754077953, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_189108973, prime_ninetyTwoCL_47930280449754077953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267229 : Nat.totient 108768553337459661411045267229 = 98682345713344710116051266800 := by
  rw [← show ((([(11, 1), (499, 1), (19815732070952753035351661, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_11, prime_ninetyTwoCL_499, prime_ninetyTwoCL_19815732070952753035351661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267230 : Nat.totient 108768553337459661411045267230 = 42833695708046990602542810240 := by
  rw [← show ((([(2, 1), (5, 1), (109, 1), (157, 1), (635590214091390530070971, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_5, prime_ninetyTwoCL_109, prime_ninetyTwoCL_157, prime_ninetyTwoCL_635590214091390530070971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267231 : Nat.totient 108768553337459661411045267231 = 72512368891639774274030178152 := by
  rw [← show ((([(3, 1), (36256184445819887137015089077, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_36256184445819887137015089077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267232 : Nat.totient 108768553337459661411045267232 = 42846518197123426818824601600 := by
  rw [← show ((([(2, 5), (7, 1), (19, 1), (41, 1), (181, 1), (17192452609, 1), (200309462473, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_7, prime_ninetyTwoCL_19, prime_ninetyTwoCL_41, prime_ninetyTwoCL_181, prime_ninetyTwoCL_17192452609, prime_ninetyTwoCL_200309462473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267233 : Nat.totient 108768553337459661411045267233 = 108768548521282924333228320000 := by
  rw [← show ((([(22617983, 1), (15814651201, 1), (304081403551, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_22617983, prime_ninetyTwoCL_15814651201, prime_ninetyTwoCL_304081403551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267234 : Nat.totient 108768553337459661411045267234 = 32148804442588685254055439360 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (29, 1), (211, 1), (2857, 1), (26588681473406728147, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_13, prime_ninetyTwoCL_29, prime_ninetyTwoCL_211, prime_ninetyTwoCL_2857, prime_ninetyTwoCL_26588681473406728147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267235 : Nat.totient 108768553337459661411045267235 = 87014842639317248913385683264 := by
  rw [← show ((([(5, 1), (2838938969, 1), (7662620051023693663, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_5, prime_ninetyTwoCL_2838938969, prime_ninetyTwoCL_7662620051023693663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267236 : Nat.totient 108768553337459661411045267236 = 52019742900524185892239040808 := by
  rw [← show ((([(2, 2), (23, 1), (1182266884102822406641796383, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_23, prime_ninetyTwoCL_1182266884102822406641796383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267237 : Nat.totient 108768553337459661411045267237 = 71127346649816727806602936320 := by
  rw [← show ((([(3, 1), (59, 1), (457, 1), (4080409, 1), (137756257, 1), (2392207541, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_59, prime_ninetyTwoCL_457, prime_ninetyTwoCL_4080409, prime_ninetyTwoCL_137756257, prime_ninetyTwoCL_2392207541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267238 : Nat.totient 108768553337459661411045267238 = 54384276668729830705522633618 := by
  rw [← show ((([(2, 1), (54384276668729830705522633619, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_54384276668729830705522633619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267239 : Nat.totient 108768553337459661411045267239 = 88888924706091653495558688768 := by
  rw [← show ((([(7, 1), (37, 1), (53, 1), (809, 1), (80269493789, 1), (122019340357, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_7, prime_ninetyTwoCL_37, prime_ninetyTwoCL_53, prime_ninetyTwoCL_809, prime_ninetyTwoCL_80269493789, prime_ninetyTwoCL_122019340357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267240 : Nat.totient 108768553337459661411045267240 = 26110943069844061597335552000 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (11, 1), (113, 1), (1667, 1), (4787, 1), (9901, 1), (361357, 1), (25540913, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_5, prime_ninetyTwoCL_11, prime_ninetyTwoCL_113, prime_ninetyTwoCL_1667, prime_ninetyTwoCL_4787, prime_ninetyTwoCL_9901, prime_ninetyTwoCL_361357, prime_ninetyTwoCL_25540913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267241 : Nat.totient 108768553337459661411045267241 = 101137024785213705305942377984 := by
  rw [← show ((([(17, 1), (83, 1), (20953581563, 1), (3678900750778937, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_17, prime_ninetyTwoCL_83, prime_ninetyTwoCL_20953581563, prime_ninetyTwoCL_3678900750778937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267242 : Nat.totient 108768553337459661411045267242 = 54384275164988187249270935500 := by
  rw [← show ((([(2, 1), (36165971, 1), (1503741643456215532151, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_36165971, prime_ninetyTwoCL_1503741643456215532151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267243 : Nat.totient 108768553337459661411045267243 = 71491000469867975349228798720 := by
  rw [← show ((([(3, 2), (71, 1), (1059889, 1), (160598730984217144933, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_71, prime_ninetyTwoCL_1059889, prime_ninetyTwoCL_160598730984217144933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267244 : Nat.totient 108768553337459661411045267244 = 53773217370623815153809350400 := by
  rw [← show ((([(2, 2), (89, 1), (5547451051, 1), (55075680956440649, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_89, prime_ninetyTwoCL_5547451051, prime_ninetyTwoCL_55075680956440649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267245 : Nat.totient 108768553337459661411045267245 = 87014842663611113319658003456 := by
  rw [← show ((([(5, 1), (13688863073, 1), (1589153938605689513, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_5, prime_ninetyTwoCL_13688863073, prime_ninetyTwoCL_1589153938605689513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267246 : Nat.totient 108768553337459661411045267246 = 30988682450480744540256211968 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (353, 1), (2813693, 1), (2607369892442200247, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_7, prime_ninetyTwoCL_353, prime_ninetyTwoCL_2813693, prime_ninetyTwoCL_2607369892442200247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267247 : Nat.totient 108768553337459661411045267247 = 100400768777852880593750818560 := by
  rw [← show ((([(13, 1), (104717, 1), (7185247, 1), (11119905747659081, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_13, prime_ninetyTwoCL_104717, prime_ninetyTwoCL_7185247, prime_ninetyTwoCL_11119905747659081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267248 : Nat.totient 108768553337459661411045267248 = 52627848102077892540258885120 := by
  rw [← show ((([(2, 4), (31, 1), (25097, 1), (8737755037668335681029, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_31, prime_ninetyTwoCL_25097, prime_ninetyTwoCL_8737755037668335681029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267249 : Nat.totient 108768553337459661411045267249 = 72067489483555415395514212416 := by
  rw [← show ((([(3, 1), (163, 1), (3949069, 1), (56324814639148593389, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_163, prime_ninetyTwoCL_3949069, prime_ninetyTwoCL_56324814639148593389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267250 : Nat.totient 108768553337459661411045267250 = 43507421325476376245277664000 := by
  rw [← show ((([(2, 1), (5, 3), (4576121681, 1), (95074878615282749, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_5, prime_ninetyTwoCL_4576121681, prime_ninetyTwoCL_95074878615282749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267251 : Nat.totient 108768553337459661411045267251 = 91680573618247786860198218400 := by
  rw [← show ((([(11, 1), (19, 1), (47, 1), (35531, 1), (311638982428429492327, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_11, prime_ninetyTwoCL_19, prime_ninetyTwoCL_47, prime_ninetyTwoCL_35531, prime_ninetyTwoCL_311638982428429492327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267252 : Nat.totient 108768553337459661411045267252 = 35561763899455134958808944896 := by
  rw [← show ((([(2, 2), (3, 3), (67, 1), (233, 1), (64513242880411759402229, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_67, prime_ninetyTwoCL_233, prime_ninetyTwoCL_64513242880411759402229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267253 : Nat.totient 108768553337459661411045267253 = 93230188574965424066610229032 := by
  rw [← show ((([(7, 2), (2219766394642033906347862597, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_7, prime_ninetyTwoCL_2219766394642033906347862597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267254 : Nat.totient 108768553337459661411045267254 = 54381809361365318078336296800 := by
  rw [← show ((([(2, 1), (24071, 1), (297589, 1), (2154791, 1), (3523361437663, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_24071, prime_ninetyTwoCL_297589, prime_ninetyTwoCL_2154791, prime_ninetyTwoCL_3523361437663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267255 : Nat.totient 108768553337459661411045267255 = 57985488830484433089574154496 := by
  rw [← show ((([(3, 1), (5, 1), (2377, 1), (35901407, 1), (84971139487535503, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_5, prime_ninetyTwoCL_2377, prime_ninetyTwoCL_35901407, prime_ninetyTwoCL_84971139487535503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267256 : Nat.totient 108768553337459661411045267256 = 54356812336009373371042667520 := by
  rw [← show ((([(2, 3), (1993, 1), (308093, 1), (211793063, 1), (104547223661, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_1993, prime_ninetyTwoCL_308093, prime_ninetyTwoCL_211793063, prime_ninetyTwoCL_104547223661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267257 : Nat.totient 108768553337459661411045267257 = 108768553337459661411045267256 := by
  rw [← show ((([(108768553337459661411045267257, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_108768553337459661411045267257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267258 : Nat.totient 108768553337459661411045267258 = 33289301967005538086924067840 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (43, 1), (821, 1), (1634486779, 1), (18480348456667, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_17, prime_ninetyTwoCL_43, prime_ninetyTwoCL_821, prime_ninetyTwoCL_1634486779, prime_ninetyTwoCL_18480348456667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267259 : Nat.totient 108768553337459661411045267259 = 104039472366296303062658093376 := by
  rw [← show ((([(23, 1), (7744057, 1), (610670548578256800869, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_23, prime_ninetyTwoCL_7744057, prime_ninetyTwoCL_610670548578256800869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267260 : Nat.totient 108768553337459661411045267260 = 34070894106209065428968494080 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (13, 1), (127, 1), (419, 1), (1123089120970601266061, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_5, prime_ninetyTwoCL_7, prime_ninetyTwoCL_13, prime_ninetyTwoCL_127, prime_ninetyTwoCL_419, prime_ninetyTwoCL_1123089120970601266061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267261 : Nat.totient 108768553337459661411045267261 = 72008677310281545157108735104 := by
  rw [← show ((([(3, 2), (149, 1), (4229, 1), (10618311727, 1), (1806264798787, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_149, prime_ninetyTwoCL_4229, prime_ninetyTwoCL_10618311727, prime_ninetyTwoCL_1806264798787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267262 : Nat.totient 108768553337459661411045267262 = 49440251517019057942542220120 := by
  rw [← show ((([(2, 1), (11, 1), (6180747490607, 1), (799907318526803, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_11, prime_ninetyTwoCL_6180747490607, prime_ninetyTwoCL_799907318526803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267263 : Nat.totient 108768553337459661411045267263 = 105017913567202431707216120088 := by
  rw [← show ((([(29, 1), (3750639770257229703829147147, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_29, prime_ninetyTwoCL_3750639770257229703829147147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267264 : Nat.totient 108768553337459661411045267264 = 36248706213513619103852654592 := by
  rw [← show ((([(2, 6), (3, 1), (4937, 1), (298427, 1), (2788939, 1), (137867489647, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_4937, prime_ninetyTwoCL_298427, prime_ninetyTwoCL_2788939, prime_ninetyTwoCL_137867489647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267265 : Nat.totient 108768553337459661411045267265 = 85911872886843488714724768000 := by
  rw [← show ((([(5, 1), (79, 1), (56701, 1), (97866917, 1), (49622613176371, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_5, prime_ninetyTwoCL_79, prime_ninetyTwoCL_56701, prime_ninetyTwoCL_97866917, prime_ninetyTwoCL_49622613176371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267266 : Nat.totient 108768553337459661411045267266 = 54384276668729830705522633632 := by
  rw [← show ((([(2, 1), (54384276668729830705522633633, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_54384276668729830705522633633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267267 : Nat.totient 108768553337459661411045267267 = 62153374399111284150277144512 := by
  rw [← show ((([(3, 1), (7, 1), (734233, 1), (7054238805435621183119, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_7, prime_ninetyTwoCL_734233, prime_ninetyTwoCL_7054238805435621183119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267268 : Nat.totient 108768553337459661411045267268 = 53638617290591963393471844864 := by
  rw [← show ((([(2, 2), (73, 1), (80263, 1), (54032009, 1), (85892253428087, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_73, prime_ninetyTwoCL_80263, prime_ninetyTwoCL_54032009, prime_ninetyTwoCL_85892253428087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267269 : Nat.totient 108768553337459661411045267269 = 108750870269123218611271070700 := by
  rw [← show ((([(6151, 1), (17683068336442799774190419, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_6151, prime_ninetyTwoCL_17683068336442799774190419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267270 : Nat.totient 108768553337459661411045267270 = 27471919533030184300532108352 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (19, 1), (4259, 1), (14934806558585899472743, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_5, prime_ninetyTwoCL_19, prime_ninetyTwoCL_4259, prime_ninetyTwoCL_14934806558585899472743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267271 : Nat.totient 108768553337459661411045267271 = 108766924161409243537074324288 := by
  rw [← show ((([(81019, 1), (379417, 1), (3538341026242234477, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_81019, prime_ninetyTwoCL_379417, prime_ninetyTwoCL_3538341026242234477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267272 : Nat.totient 108768553337459661411045267272 = 53856273982625657591876782416 := by
  rw [← show ((([(2, 3), (103, 1), (132000671526043278411462703, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_103, prime_ninetyTwoCL_132000671526043278411462703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267273 : Nat.totient 108768553337459661411045267273 = 59365405198569802705613721600 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (41, 1), (557065281833, 1), (11100846842429, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_11, prime_ninetyTwoCL_13, prime_ninetyTwoCL_41, prime_ninetyTwoCL_557065281833, prime_ninetyTwoCL_11100846842429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267274 : Nat.totient 108768553337459661411045267274 = 46615094284705195529810178000 := by
  rw [← show ((([(2, 1), (7, 1), (16783013141, 1), (462919400466142951, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_7, prime_ninetyTwoCL_16783013141, prime_ninetyTwoCL_462919400466142951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267275 : Nat.totient 108768553337459661411045267275 = 80193638707971846430631731200 := by
  rw [← show ((([(5, 2), (17, 1), (61, 1), (239, 1), (3823, 1), (40099, 1), (863123, 1), (132671047, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_5, prime_ninetyTwoCL_17, prime_ninetyTwoCL_61, prime_ninetyTwoCL_239, prime_ninetyTwoCL_3823, prime_ninetyTwoCL_40099, prime_ninetyTwoCL_863123, prime_ninetyTwoCL_132671047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267276 : Nat.totient 108768553337459661411045267276 = 35276270256996330361609797120 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (2037689, 1), (120221593790079227461, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_37, prime_ninetyTwoCL_2037689, prime_ninetyTwoCL_120221593790079227461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267277 : Nat.totient 108768553337459661411045267277 = 108580046309494196998039345152 := by
  rw [← show ((([(577, 1), (34832995957, 1), (5411737338958393, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_577, prime_ninetyTwoCL_34832995957, prime_ninetyTwoCL_5411737338958393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267278 : Nat.totient 108768553337459661411045267278 = 54358827779320036680859307856 := by
  rw [← show ((([(2, 1), (2137, 1), (25448889409794024663323647, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_2137, prime_ninetyTwoCL_25448889409794024663323647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267279 : Nat.totient 108768553337459661411045267279 = 69412062921243039723350016000 := by
  rw [← show ((([(3, 3), (31, 1), (101, 1), (1429, 1), (3929, 1), (573329, 1), (399703870003, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_31, prime_ninetyTwoCL_101, prime_ninetyTwoCL_1429, prime_ninetyTwoCL_3929, prime_ninetyTwoCL_573329, prime_ninetyTwoCL_399703870003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267280 : Nat.totient 108768553337459661411045267280 = 43453404606166581370457341440 := by
  rw [← show ((([(2, 4), (5, 1), (811, 1), (117413, 1), (14278294202820937687, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_5, prime_ninetyTwoCL_811, prime_ninetyTwoCL_117413, prime_ninetyTwoCL_14278294202820937687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267281 : Nat.totient 108768553337459661411045267281 = 93005317004692244102746177536 := by
  rw [← show ((([(7, 1), (433, 1), (11677, 1), (83089, 1), (196073, 1), (188636100379, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_7, prime_ninetyTwoCL_433, prime_ninetyTwoCL_11677, prime_ninetyTwoCL_83089, prime_ninetyTwoCL_196073, prime_ninetyTwoCL_188636100379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267282 : Nat.totient 108768553337459661411045267282 = 34679828600349457261492693872 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (788177922735214937761197589, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_23, prime_ninetyTwoCL_788177922735214937761197589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267283 : Nat.totient 108768553337459661411045267283 = 107737249575947041736503776000 := by
  rw [← show ((([(107, 1), (13159, 1), (16361, 1), (79732171, 1), (59217934261, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_107, prime_ninetyTwoCL_13159, prime_ninetyTwoCL_16361, prime_ninetyTwoCL_79732171, prime_ninetyTwoCL_59217934261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267284 : Nat.totient 108768553337459661411045267284 = 49351112522098545641742581760 := by
  rw [← show ((([(2, 2), (11, 1), (557, 1), (130969, 1), (97860083, 1), (346275200449, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_11, prime_ninetyTwoCL_557, prime_ninetyTwoCL_130969, prime_ninetyTwoCL_97860083, prime_ninetyTwoCL_346275200449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267285 : Nat.totient 108768553337459661411045267285 = 58009515677294626022200166400 := by
  rw [← show ((([(3, 1), (5, 1), (159673, 1), (3596003, 1), (12628755722633201, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_5, prime_ninetyTwoCL_159673, prime_ninetyTwoCL_3596003, prime_ninetyTwoCL_12628755722633201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267286 : Nat.totient 108768553337459661411045267286 = 50200870753406888497707141600 := by
  rw [← show ((([(2, 1), (13, 1), (2831673541, 1), (1477361650989344171, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_13, prime_ninetyTwoCL_2831673541, prime_ninetyTwoCL_1477361650989344171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267287 : Nat.totient 108768553337459661411045267287 = 108768553336651408236869406576 := by
  rw [← show ((([(134572402463, 1), (808253039603458249, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_134572402463, prime_ninetyTwoCL_808253039603458249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267288 : Nat.totient 108768553337459661411045267288 = 31076729524988474688870076224 := by
  rw [← show ((([(2, 3), (3, 2), (7, 1), (215810621701308852006042197, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_7, prime_ninetyTwoCL_215810621701308852006042197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267289 : Nat.totient 108768553337459661411045267289 = 102826803810395895376973442048 := by
  rw [← show ((([(19, 1), (479, 1), (57847, 1), (605257, 1), (6227737, 1), (54810443, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_19, prime_ninetyTwoCL_479, prime_ninetyTwoCL_57847, prime_ninetyTwoCL_605257, prime_ninetyTwoCL_6227737, prime_ninetyTwoCL_54810443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267290 : Nat.totient 108768553337459661411045267290 = 43507421334983864564418106912 := by
  rw [← show ((([(2, 1), (5, 1), (10876855333745966141104526729, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_5, prime_ninetyTwoCL_10876855333745966141104526729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267291 : Nat.totient 108768553337459661411045267291 = 72505615653784896344146647360 := by
  rw [← show ((([(3, 1), (10889, 1), (771283, 1), (4316983022176680731, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_10889, prime_ninetyTwoCL_771283, prime_ninetyTwoCL_4316983022176680731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267292 : Nat.totient 108768553337459661411045267292 = 48487738117598459034630259712 := by
  rw [← show ((([(2, 2), (17, 1), (29, 1), (53, 1), (1040688060559719673648487, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_17, prime_ninetyTwoCL_29, prime_ninetyTwoCL_53, prime_ninetyTwoCL_1040688060559719673648487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267293 : Nat.totient 108768553337459661411045267293 = 108764151356265057839010314208 := by
  rw [← show ((([(24709, 1), (4401981194603572034928377, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_24709, prime_ninetyTwoCL_4401981194603572034928377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267294 : Nat.totient 108768553337459661411045267294 = 36256184445819887137015089096 := by
  rw [← show ((([(2, 1), (3, 1), (18128092222909943568507544549, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_18128092222909943568507544549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267295 : Nat.totient 108768553337459661411045267295 = 67668788559177071624821800960 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (503, 1), (365569, 1), (62266199, 1), (24674759119, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_5, prime_ninetyTwoCL_7, prime_ninetyTwoCL_11, prime_ninetyTwoCL_503, prime_ninetyTwoCL_365569, prime_ninetyTwoCL_62266199, prime_ninetyTwoCL_24674759119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267296 : Nat.totient 108768553337459661411045267296 = 53462509267564918320683266048 := by
  rw [← show ((([(2, 5), (59, 1), (57610462572807024052460417, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_59, prime_ninetyTwoCL_57610462572807024052460417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267297 : Nat.totient 108768553337459661411045267297 = 72491684420361963238504716768 := by
  rw [← show ((([(3, 2), (5483, 1), (9719, 1), (226788492838311462029, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_3, prime_ninetyTwoCL_5483, prime_ninetyTwoCL_9719, prime_ninetyTwoCL_226788492838311462029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267298 : Nat.totient 108768553337459661411045267298 = 53227164399182387499022152036 := by
  rw [← show ((([(2, 1), (47, 1), (1157112269547443206500481567, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_47, prime_ninetyTwoCL_1157112269547443206500481567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267299 : Nat.totient 108768553337459661411045267299 = 100256287058427464431286736384 := by
  rw [← show ((([(13, 1), (839, 1), (3889, 1), (1771538299, 1), (1447469929387, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_13, prime_ninetyTwoCL_839, prime_ninetyTwoCL_3889, prime_ninetyTwoCL_1771538299, prime_ninetyTwoCL_1447469929387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267300 : Nat.totient 108768553337459661411045267300 = 28999964736068885885289600000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (5821, 1), (3305345551, 1), (18843762834121, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_2, prime_ninetyTwoCL_3, prime_ninetyTwoCL_5, prime_ninetyTwoCL_5821, prime_ninetyTwoCL_3305345551, prime_ninetyTwoCL_18843762834121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyTwoCL_108768553337459661411045267301 : Nat.totient 108768553337459661411045267301 = 106238588977981189791635045472 := by
  rw [← show ((([(43, 1), (229399, 1), (11026644581737665105193, 1)] : List FactorBlock).map factorBlockValue).prod) = 108768553337459661411045267301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyTwoCL_43, prime_ninetyTwoCL_229399, prime_ninetyTwoCL_11026644581737665105193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyTwoCL : certifiedKill 1 108768553337459661411045267199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyTwoCL_108768553337459661411045267200, phi_ninetyTwoCL_108768553337459661411045267201, phi_ninetyTwoCL_108768553337459661411045267202,
    phi_ninetyTwoCL_108768553337459661411045267203, phi_ninetyTwoCL_108768553337459661411045267204, phi_ninetyTwoCL_108768553337459661411045267205,
    phi_ninetyTwoCL_108768553337459661411045267206, phi_ninetyTwoCL_108768553337459661411045267207, phi_ninetyTwoCL_108768553337459661411045267208,
    phi_ninetyTwoCL_108768553337459661411045267209, phi_ninetyTwoCL_108768553337459661411045267210, phi_ninetyTwoCL_108768553337459661411045267211,
    phi_ninetyTwoCL_108768553337459661411045267212, phi_ninetyTwoCL_108768553337459661411045267213, phi_ninetyTwoCL_108768553337459661411045267214,
    phi_ninetyTwoCL_108768553337459661411045267215, phi_ninetyTwoCL_108768553337459661411045267216, phi_ninetyTwoCL_108768553337459661411045267217,
    phi_ninetyTwoCL_108768553337459661411045267218, phi_ninetyTwoCL_108768553337459661411045267219, phi_ninetyTwoCL_108768553337459661411045267220,
    phi_ninetyTwoCL_108768553337459661411045267221, phi_ninetyTwoCL_108768553337459661411045267222, phi_ninetyTwoCL_108768553337459661411045267223,
    phi_ninetyTwoCL_108768553337459661411045267224, phi_ninetyTwoCL_108768553337459661411045267225, phi_ninetyTwoCL_108768553337459661411045267226,
    phi_ninetyTwoCL_108768553337459661411045267227, phi_ninetyTwoCL_108768553337459661411045267228, phi_ninetyTwoCL_108768553337459661411045267229,
    phi_ninetyTwoCL_108768553337459661411045267230, phi_ninetyTwoCL_108768553337459661411045267231, phi_ninetyTwoCL_108768553337459661411045267232,
    phi_ninetyTwoCL_108768553337459661411045267233, phi_ninetyTwoCL_108768553337459661411045267234, phi_ninetyTwoCL_108768553337459661411045267235,
    phi_ninetyTwoCL_108768553337459661411045267236, phi_ninetyTwoCL_108768553337459661411045267237, phi_ninetyTwoCL_108768553337459661411045267238,
    phi_ninetyTwoCL_108768553337459661411045267239, phi_ninetyTwoCL_108768553337459661411045267240, phi_ninetyTwoCL_108768553337459661411045267241,
    phi_ninetyTwoCL_108768553337459661411045267242, phi_ninetyTwoCL_108768553337459661411045267243, phi_ninetyTwoCL_108768553337459661411045267244,
    phi_ninetyTwoCL_108768553337459661411045267245, phi_ninetyTwoCL_108768553337459661411045267246, phi_ninetyTwoCL_108768553337459661411045267247,
    phi_ninetyTwoCL_108768553337459661411045267248, phi_ninetyTwoCL_108768553337459661411045267249, phi_ninetyTwoCL_108768553337459661411045267250,
    phi_ninetyTwoCL_108768553337459661411045267251, phi_ninetyTwoCL_108768553337459661411045267252, phi_ninetyTwoCL_108768553337459661411045267253,
    phi_ninetyTwoCL_108768553337459661411045267254, phi_ninetyTwoCL_108768553337459661411045267255, phi_ninetyTwoCL_108768553337459661411045267256,
    phi_ninetyTwoCL_108768553337459661411045267257, phi_ninetyTwoCL_108768553337459661411045267258, phi_ninetyTwoCL_108768553337459661411045267259,
    phi_ninetyTwoCL_108768553337459661411045267260, phi_ninetyTwoCL_108768553337459661411045267261, phi_ninetyTwoCL_108768553337459661411045267262,
    phi_ninetyTwoCL_108768553337459661411045267263, phi_ninetyTwoCL_108768553337459661411045267264, phi_ninetyTwoCL_108768553337459661411045267265,
    phi_ninetyTwoCL_108768553337459661411045267266, phi_ninetyTwoCL_108768553337459661411045267267, phi_ninetyTwoCL_108768553337459661411045267268,
    phi_ninetyTwoCL_108768553337459661411045267269, phi_ninetyTwoCL_108768553337459661411045267270, phi_ninetyTwoCL_108768553337459661411045267271,
    phi_ninetyTwoCL_108768553337459661411045267272, phi_ninetyTwoCL_108768553337459661411045267273, phi_ninetyTwoCL_108768553337459661411045267274,
    phi_ninetyTwoCL_108768553337459661411045267275, phi_ninetyTwoCL_108768553337459661411045267276, phi_ninetyTwoCL_108768553337459661411045267277,
    phi_ninetyTwoCL_108768553337459661411045267278, phi_ninetyTwoCL_108768553337459661411045267279, phi_ninetyTwoCL_108768553337459661411045267280,
    phi_ninetyTwoCL_108768553337459661411045267281, phi_ninetyTwoCL_108768553337459661411045267282, phi_ninetyTwoCL_108768553337459661411045267283,
    phi_ninetyTwoCL_108768553337459661411045267284, phi_ninetyTwoCL_108768553337459661411045267285, phi_ninetyTwoCL_108768553337459661411045267286,
    phi_ninetyTwoCL_108768553337459661411045267287, phi_ninetyTwoCL_108768553337459661411045267288, phi_ninetyTwoCL_108768553337459661411045267289,
    phi_ninetyTwoCL_108768553337459661411045267290, phi_ninetyTwoCL_108768553337459661411045267291, phi_ninetyTwoCL_108768553337459661411045267292,
    phi_ninetyTwoCL_108768553337459661411045267293, phi_ninetyTwoCL_108768553337459661411045267294, phi_ninetyTwoCL_108768553337459661411045267295,
    phi_ninetyTwoCL_108768553337459661411045267296, phi_ninetyTwoCL_108768553337459661411045267297, phi_ninetyTwoCL_108768553337459661411045267298,
    phi_ninetyTwoCL_108768553337459661411045267299, phi_ninetyTwoCL_108768553337459661411045267300, phi_ninetyTwoCL_108768553337459661411045267301]

end TotientTailPeriodKiller
end Erdos249257
