import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTenDDFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTenDDFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTenDDFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTenDDFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTenDDFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTenDDFastPow a n * oneHundredTenDDFastPow a n * a else oneHundredTenDDFastPow a n * oneHundredTenDDFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTenDD_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTenDD_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTenDD_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTenDD_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTenDD_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTenDD_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTenDD_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTenDD_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTenDD_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTenDD_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTenDD_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTenDD_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTenDD_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTenDD_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTenDD_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTenDD_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTenDD_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTenDD_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTenDD_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTenDD_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTenDD_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTenDD_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTenDD_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTenDD_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTenDD_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTenDD_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTenDD_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTenDD_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTenDD_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTenDD_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTenDD_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTenDD_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTenDD_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTenDD_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTenDD_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTenDD_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTenDD_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTenDD_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTenDD_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTenDD_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTenDD_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTenDD_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTenDD_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTenDD_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTenDD_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTenDD_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTenDD_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTenDD_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTenDD_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTenDD_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTenDD_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTenDD_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTenDD_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTenDD_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTenDD_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTenDD_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredTenDD_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTenDD_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTenDD_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTenDD_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTenDD_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredTenDD_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredTenDD_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTenDD_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredTenDD_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredTenDD_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTenDD_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTenDD_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTenDD_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredTenDD_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTenDD_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredTenDD_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredTenDD_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredTenDD_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTenDD_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTenDD_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredTenDD_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredTenDD_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredTenDD_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTenDD_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredTenDD_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredTenDD_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredTenDD_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredTenDD_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredTenDD_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredTenDD_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredTenDD_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredTenDD_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredTenDD_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredTenDD_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredTenDD_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredTenDD_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredTenDD_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredTenDD_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredTenDD_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredTenDD_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredTenDD_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTenDD_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredTenDD_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredTenDD_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredTenDD_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredTenDD_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredTenDD_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredTenDD_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredTenDD_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredTenDD_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredTenDD_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredTenDD_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredTenDD_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredTenDD_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredTenDD_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredTenDD_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredTenDD_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredTenDD_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredTenDD_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredTenDD_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredTenDD_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredTenDD_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredTenDD_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredTenDD_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTenDD_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredTenDD_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTenDD_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredTenDD_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredTenDD_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredTenDD_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredTenDD_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_oneHundredTenDD_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_oneHundredTenDD_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_oneHundredTenDD_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_oneHundredTenDD_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredTenDD_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredTenDD_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_oneHundredTenDD_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_oneHundredTenDD_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredTenDD_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredTenDD_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredTenDD_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredTenDD_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredTenDD_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_oneHundredTenDD_3251 : Nat.Prime 3251 := by norm_num

private theorem prime_oneHundredTenDD_3257 : Nat.Prime 3257 := by norm_num

private theorem prime_oneHundredTenDD_3373 : Nat.Prime 3373 := by norm_num

private theorem prime_oneHundredTenDD_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredTenDD_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_oneHundredTenDD_3727 : Nat.Prime 3727 := by norm_num

private theorem prime_oneHundredTenDD_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_oneHundredTenDD_3851 : Nat.Prime 3851 := by norm_num

private theorem prime_oneHundredTenDD_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredTenDD_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_oneHundredTenDD_4051 : Nat.Prime 4051 := by norm_num

private theorem prime_oneHundredTenDD_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredTenDD_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_oneHundredTenDD_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredTenDD_4261 : Nat.Prime 4261 := by norm_num

private theorem prime_oneHundredTenDD_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_oneHundredTenDD_4447 : Nat.Prime 4447 := by norm_num

private theorem prime_oneHundredTenDD_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_oneHundredTenDD_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredTenDD_4931 : Nat.Prime 4931 := by norm_num

private theorem prime_oneHundredTenDD_4951 : Nat.Prime 4951 := by norm_num

private theorem prime_oneHundredTenDD_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_oneHundredTenDD_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_oneHundredTenDD_5659 : Nat.Prime 5659 := by norm_num

private theorem prime_oneHundredTenDD_5879 : Nat.Prime 5879 := by norm_num

private theorem prime_oneHundredTenDD_6151 : Nat.Prime 6151 := by norm_num

private theorem prime_oneHundredTenDD_6203 : Nat.Prime 6203 := by norm_num

private theorem prime_oneHundredTenDD_6217 : Nat.Prime 6217 := by norm_num

private theorem prime_oneHundredTenDD_6947 : Nat.Prime 6947 := by norm_num

private theorem prime_oneHundredTenDD_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_oneHundredTenDD_7027 : Nat.Prime 7027 := by norm_num

private theorem prime_oneHundredTenDD_7129 : Nat.Prime 7129 := by norm_num

private theorem prime_oneHundredTenDD_7477 : Nat.Prime 7477 := by norm_num

private theorem prime_oneHundredTenDD_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_oneHundredTenDD_7703 : Nat.Prime 7703 := by norm_num

private theorem prime_oneHundredTenDD_7727 : Nat.Prime 7727 := by norm_num

private theorem prime_oneHundredTenDD_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_oneHundredTenDD_8081 : Nat.Prime 8081 := by norm_num

private theorem prime_oneHundredTenDD_8237 : Nat.Prime 8237 := by norm_num

private theorem prime_oneHundredTenDD_8263 : Nat.Prime 8263 := by norm_num

private theorem prime_oneHundredTenDD_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredTenDD_8311 : Nat.Prime 8311 := by norm_num

private theorem prime_oneHundredTenDD_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredTenDD_9013 : Nat.Prime 9013 := by norm_num

private theorem prime_oneHundredTenDD_9049 : Nat.Prime 9049 := by norm_num

private theorem prime_oneHundredTenDD_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredTenDD_10111 : Nat.Prime 10111 := by norm_num

private theorem prime_oneHundredTenDD_10333 : Nat.Prime 10333 := by norm_num

private theorem prime_oneHundredTenDD_11083 : Nat.Prime 11083 := by norm_num

private theorem prime_oneHundredTenDD_11527 : Nat.Prime 11527 := by norm_num

private theorem prime_oneHundredTenDD_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredTenDD_11863 : Nat.Prime 11863 := by norm_num

private theorem prime_oneHundredTenDD_12437 : Nat.Prime 12437 := by norm_num

private theorem prime_oneHundredTenDD_12511 : Nat.Prime 12511 := by norm_num

private theorem prime_oneHundredTenDD_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredTenDD_12601 : Nat.Prime 12601 := by norm_num

private theorem prime_oneHundredTenDD_12809 : Nat.Prime 12809 := by norm_num

private theorem prime_oneHundredTenDD_12893 : Nat.Prime 12893 := by norm_num

private theorem prime_oneHundredTenDD_13781 : Nat.Prime 13781 := by norm_num

private theorem prime_oneHundredTenDD_13873 : Nat.Prime 13873 := by norm_num

private theorem prime_oneHundredTenDD_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredTenDD_15173 : Nat.Prime 15173 := by norm_num

private theorem prime_oneHundredTenDD_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredTenDD_15679 : Nat.Prime 15679 := by norm_num

private theorem prime_oneHundredTenDD_15787 : Nat.Prime 15787 := by norm_num

private theorem prime_oneHundredTenDD_16963 : Nat.Prime 16963 := by norm_num

private theorem prime_oneHundredTenDD_17117 : Nat.Prime 17117 := by norm_num

private theorem prime_oneHundredTenDD_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTenDD_18257 : Nat.Prime 18257 := by norm_num

private theorem prime_oneHundredTenDD_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_oneHundredTenDD_19577 : Nat.Prime 19577 := by norm_num

private theorem prime_oneHundredTenDD_19853 : Nat.Prime 19853 := by norm_num

private theorem prime_oneHundredTenDD_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTenDD_21557 : Nat.Prime 21557 := by norm_num

private theorem prime_oneHundredTenDD_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredTenDD_21751 : Nat.Prime 21751 := by norm_num

private theorem prime_oneHundredTenDD_22441 : Nat.Prime 22441 := by norm_num

private theorem prime_oneHundredTenDD_23017 : Nat.Prime 23017 := by norm_num

private theorem prime_oneHundredTenDD_23971 : Nat.Prime 23971 := by norm_num

private theorem prime_oneHundredTenDD_25537 : Nat.Prime 25537 := by norm_num

private theorem prime_oneHundredTenDD_26021 : Nat.Prime 26021 := by norm_num

private theorem prime_oneHundredTenDD_29537 : Nat.Prime 29537 := by norm_num

private theorem prime_oneHundredTenDD_30047 : Nat.Prime 30047 := by norm_num

private theorem prime_oneHundredTenDD_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredTenDD_31667 : Nat.Prime 31667 := by norm_num

private theorem prime_oneHundredTenDD_32183 : Nat.Prime 32183 := by norm_num

private theorem prime_oneHundredTenDD_33493 : Nat.Prime 33493 := by norm_num

private theorem prime_oneHundredTenDD_35267 : Nat.Prime 35267 := by norm_num

private theorem prime_oneHundredTenDD_38317 : Nat.Prime 38317 := by norm_num

private theorem prime_oneHundredTenDD_38933 : Nat.Prime 38933 := by norm_num

private theorem prime_oneHundredTenDD_39343 : Nat.Prime 39343 := by norm_num

private theorem prime_oneHundredTenDD_39619 : Nat.Prime 39619 := by norm_num

private theorem prime_oneHundredTenDD_42571 : Nat.Prime 42571 := by norm_num

private theorem prime_oneHundredTenDD_42577 : Nat.Prime 42577 := by norm_num

private theorem prime_oneHundredTenDD_42589 : Nat.Prime 42589 := by norm_num

private theorem prime_oneHundredTenDD_43759 : Nat.Prime 43759 := by norm_num

private theorem prime_oneHundredTenDD_44159 : Nat.Prime 44159 := by norm_num

private theorem prime_oneHundredTenDD_44221 : Nat.Prime 44221 := by norm_num

private theorem prime_oneHundredTenDD_44549 : Nat.Prime 44549 := by norm_num

private theorem prime_oneHundredTenDD_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredTenDD_49823 : Nat.Prime 49823 := by norm_num

private theorem prime_oneHundredTenDD_55373 : Nat.Prime 55373 := by norm_num

private theorem prime_oneHundredTenDD_55927 : Nat.Prime 55927 := by norm_num

private theorem prime_oneHundredTenDD_59723 : Nat.Prime 59723 := by norm_num

private theorem prime_oneHundredTenDD_61471 : Nat.Prime 61471 := by norm_num

private theorem prime_oneHundredTenDD_68351 : Nat.Prime 68351 := by norm_num

private theorem prime_oneHundredTenDD_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredTenDD_70289 : Nat.Prime 70289 := by norm_num

private theorem prime_oneHundredTenDD_70729 : Nat.Prime 70729 := by norm_num

private theorem prime_oneHundredTenDD_71887 : Nat.Prime 71887 := by norm_num

private theorem prime_oneHundredTenDD_72211 : Nat.Prime 72211 := by norm_num

private theorem prime_oneHundredTenDD_78347 : Nat.Prime 78347 := by norm_num

private theorem prime_oneHundredTenDD_83639 : Nat.Prime 83639 := by norm_num

private theorem prime_oneHundredTenDD_83903 : Nat.Prime 83903 := by norm_num

private theorem prime_oneHundredTenDD_86381 : Nat.Prime 86381 := by norm_num

private theorem prime_oneHundredTenDD_89317 : Nat.Prime 89317 := by norm_num

private theorem prime_oneHundredTenDD_91753 : Nat.Prime 91753 := by norm_num

private theorem prime_oneHundredTenDD_92203 : Nat.Prime 92203 := by norm_num

private theorem prime_oneHundredTenDD_93083 : Nat.Prime 93083 := by norm_num

private theorem prime_oneHundredTenDD_96697 : Nat.Prime 96697 := by norm_num

private theorem prime_oneHundredTenDD_97429 : Nat.Prime 97429 := by norm_num

private theorem prime_oneHundredTenDD_98729 : Nat.Prime 98729 := by norm_num

private theorem prime_oneHundredTenDD_100271 : Nat.Prime 100271 := by norm_num

private theorem prime_oneHundredTenDD_105239 : Nat.Prime 105239 := by norm_num

private theorem prime_oneHundredTenDD_114773 : Nat.Prime 114773 := by norm_num

private theorem prime_oneHundredTenDD_126823 : Nat.Prime 126823 := by norm_num

private theorem prime_oneHundredTenDD_141793 : Nat.Prime 141793 := by norm_num

private theorem prime_oneHundredTenDD_144223 : Nat.Prime 144223 := by norm_num

private theorem prime_oneHundredTenDD_160813 : Nat.Prime 160813 := by norm_num

private theorem prime_oneHundredTenDD_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTenDD_180233 : Nat.Prime 180233 := by norm_num

private theorem prime_oneHundredTenDD_183569 : Nat.Prime 183569 := by norm_num

private theorem prime_oneHundredTenDD_184631 : Nat.Prime 184631 := by norm_num

private theorem prime_oneHundredTenDD_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredTenDD_189439 : Nat.Prime 189439 := by norm_num

private theorem prime_oneHundredTenDD_203233 : Nat.Prime 203233 := by norm_num

private theorem prime_oneHundredTenDD_221071 : Nat.Prime 221071 := by norm_num

private theorem prime_oneHundredTenDD_223759 : Nat.Prime 223759 := by norm_num

private theorem prime_oneHundredTenDD_229841 : Nat.Prime 229841 := by norm_num

private theorem prime_oneHundredTenDD_248707 : Nat.Prime 248707 := by norm_num

private theorem prime_oneHundredTenDD_261823 : Nat.Prime 261823 := by norm_num

private theorem prime_oneHundredTenDD_264889 : Nat.Prime 264889 := by norm_num

private theorem prime_oneHundredTenDD_274117 : Nat.Prime 274117 := by norm_num

private theorem prime_oneHundredTenDD_279029 : Nat.Prime 279029 := by norm_num

private theorem prime_oneHundredTenDD_282001 : Nat.Prime 282001 := by norm_num

private theorem prime_oneHundredTenDD_289439 : Nat.Prime 289439 := by norm_num

private theorem prime_oneHundredTenDD_298451 : Nat.Prime 298451 := by norm_num

private theorem prime_oneHundredTenDD_316271 : Nat.Prime 316271 := by norm_num

private theorem prime_oneHundredTenDD_335249 : Nat.Prime 335249 := by norm_num

private theorem prime_oneHundredTenDD_351257 : Nat.Prime 351257 := by norm_num

private theorem prime_oneHundredTenDD_353501 : Nat.Prime 353501 := by norm_num

private theorem prime_oneHundredTenDD_366853 : Nat.Prime 366853 := by norm_num

private theorem prime_oneHundredTenDD_368873 : Nat.Prime 368873 := by norm_num

private theorem prime_oneHundredTenDD_371387 : Nat.Prime 371387 := by norm_num

private theorem prime_oneHundredTenDD_377137 : Nat.Prime 377137 := by norm_num

private theorem prime_oneHundredTenDD_382883 : Nat.Prime 382883 := by norm_num

private theorem prime_oneHundredTenDD_393013 : Nat.Prime 393013 := by norm_num

private theorem prime_oneHundredTenDD_405749 : Nat.Prime 405749 := by norm_num

private theorem prime_oneHundredTenDD_450277 : Nat.Prime 450277 := by norm_num

private theorem prime_oneHundredTenDD_454231 : Nat.Prime 454231 := by norm_num

private theorem prime_oneHundredTenDD_463891 : Nat.Prime 463891 := by norm_num

private theorem prime_oneHundredTenDD_470333 : Nat.Prime 470333 := by norm_num

private theorem prime_oneHundredTenDD_479861 : Nat.Prime 479861 := by norm_num

private theorem prime_oneHundredTenDD_485567 : Nat.Prime 485567 := by norm_num

private theorem prime_oneHundredTenDD_488417 : Nat.Prime 488417 := by norm_num

private theorem prime_oneHundredTenDD_528289 : Nat.Prime 528289 := by norm_num

private theorem prime_oneHundredTenDD_536563 : Nat.Prime 536563 := by norm_num

private theorem prime_oneHundredTenDD_546151 : Nat.Prime 546151 := by norm_num

private theorem prime_oneHundredTenDD_555349 : Nat.Prime 555349 := by norm_num

private theorem prime_oneHundredTenDD_571397 : Nat.Prime 571397 := by norm_num

private theorem prime_oneHundredTenDD_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredTenDD_670673 : Nat.Prime 670673 := by norm_num

private theorem prime_oneHundredTenDD_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredTenDD_724481 : Nat.Prime 724481 := by norm_num

private theorem prime_oneHundredTenDD_758111 : Nat.Prime 758111 := by norm_num

private theorem prime_oneHundredTenDD_791773 : Nat.Prime 791773 := by norm_num

private theorem prime_oneHundredTenDD_800243 : Nat.Prime 800243 := by norm_num

private theorem prime_oneHundredTenDD_809243 : Nat.Prime 809243 := by norm_num

private theorem prime_oneHundredTenDD_847991 : Nat.Prime 847991 := by norm_num

private theorem prime_oneHundredTenDD_952741 : Nat.Prime 952741 := by norm_num

private theorem prime_oneHundredTenDD_1004167 : Nat.Prime 1004167 := by norm_num

private theorem prime_oneHundredTenDD_1089503 : Nat.Prime 1089503 := by norm_num

private theorem prime_oneHundredTenDD_1128371 : Nat.Prime 1128371 := by norm_num

private theorem prime_oneHundredTenDD_1276397 : Nat.Prime 1276397 := by norm_num

private theorem prime_oneHundredTenDD_1333901 : Nat.Prime 1333901 := by norm_num

private theorem prime_oneHundredTenDD_1382327 : Nat.Prime 1382327 := by norm_num

private theorem prime_oneHundredTenDD_1473083 : Nat.Prime 1473083 := by norm_num

private theorem prime_oneHundredTenDD_1625321 : Nat.Prime 1625321 := by norm_num

private theorem prime_oneHundredTenDD_1650991 : Nat.Prime 1650991 := by norm_num

private theorem prime_oneHundredTenDD_1652899 : Nat.Prime 1652899 := by norm_num

private theorem prime_oneHundredTenDD_1682531 : Nat.Prime 1682531 := by norm_num

private theorem prime_oneHundredTenDD_1826549 : Nat.Prime 1826549 := by norm_num

private theorem prime_oneHundredTenDD_1827127 : Nat.Prime 1827127 := by norm_num

private theorem prime_oneHundredTenDD_2046487 : Nat.Prime 2046487 := by norm_num

private theorem prime_oneHundredTenDD_2186603 : Nat.Prime 2186603 := by norm_num

private theorem prime_oneHundredTenDD_2327173 : Nat.Prime 2327173 := by norm_num

private theorem prime_oneHundredTenDD_2359067 : Nat.Prime 2359067 := by norm_num

private theorem prime_oneHundredTenDD_2404357 : Nat.Prime 2404357 := by norm_num

private theorem prime_oneHundredTenDD_2444899 : Nat.Prime 2444899 := by norm_num

private theorem prime_oneHundredTenDD_2492701 : Nat.Prime 2492701 := by norm_num

private theorem prime_oneHundredTenDD_2668993 : Nat.Prime 2668993 := by norm_num

private theorem prime_oneHundredTenDD_2684477 : Nat.Prime 2684477 := by norm_num

private theorem prime_oneHundredTenDD_2880121 : Nat.Prime 2880121 := by norm_num

private theorem prime_oneHundredTenDD_2893777 : Nat.Prime 2893777 := by norm_num

private theorem prime_oneHundredTenDD_2908721 : Nat.Prime 2908721 := by norm_num

private theorem prime_oneHundredTenDD_3148051 : Nat.Prime 3148051 := by norm_num

private theorem prime_oneHundredTenDD_3154799 : Nat.Prime 3154799 := by norm_num

private theorem prime_oneHundredTenDD_3165203 : Nat.Prime 3165203 := by norm_num

private theorem prime_oneHundredTenDD_3283807 : Nat.Prime 3283807 := by norm_num

private theorem prime_oneHundredTenDD_3353087 : Nat.Prime 3353087 := by norm_num

private theorem prime_oneHundredTenDD_3552947 : Nat.Prime 3552947 := by norm_num

private theorem prime_oneHundredTenDD_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredTenDD_3692063 : Nat.Prime 3692063 := by norm_num

private theorem prime_oneHundredTenDD_3700691 : Nat.Prime 3700691 := by norm_num

private theorem prime_oneHundredTenDD_3912509 : Nat.Prime 3912509 := by norm_num

private theorem prime_oneHundredTenDD_3962759 : Nat.Prime 3962759 := by norm_num

private theorem prime_oneHundredTenDD_4015201 : Nat.Prime 4015201 := by norm_num

private theorem prime_oneHundredTenDD_4178219 : Nat.Prime 4178219 := by norm_num

private theorem prime_oneHundredTenDD_4186181 : Nat.Prime 4186181 := by norm_num

private theorem prime_oneHundredTenDD_4362719 : Nat.Prime 4362719 := by norm_num

private theorem prime_oneHundredTenDD_4365113 : Nat.Prime 4365113 := by norm_num

private theorem prime_oneHundredTenDD_4445153 : Nat.Prime 4445153 := by norm_num

private theorem prime_oneHundredTenDD_4631749 : Nat.Prime 4631749 := by norm_num

private theorem prime_oneHundredTenDD_4663781 : Nat.Prime 4663781 := by norm_num

private theorem prime_oneHundredTenDD_5154157 : Nat.Prime 5154157 := by norm_num

private theorem prime_oneHundredTenDD_5281151 : Nat.Prime 5281151 := by norm_num

private theorem prime_oneHundredTenDD_5351669 : Nat.Prime 5351669 := by norm_num

private theorem prime_oneHundredTenDD_5601787 : Nat.Prime 5601787 := by norm_num

private theorem prime_oneHundredTenDD_5760091 : Nat.Prime 5760091 := by norm_num

private theorem prime_oneHundredTenDD_5794343 : Nat.Prime 5794343 := by norm_num

private theorem prime_oneHundredTenDD_5930381 : Nat.Prime 5930381 := by norm_num

private theorem prime_oneHundredTenDD_6266849 : Nat.Prime 6266849 := by norm_num

private theorem prime_oneHundredTenDD_6444443 : Nat.Prime 6444443 := by norm_num

private theorem prime_oneHundredTenDD_6829139 : Nat.Prime 6829139 := by norm_num

private theorem prime_oneHundredTenDD_8146423 : Nat.Prime 8146423 := by norm_num

private theorem prime_oneHundredTenDD_8348687 : Nat.Prime 8348687 := by norm_num

private theorem prime_oneHundredTenDD_8406539 : Nat.Prime 8406539 := by norm_num

private theorem prime_oneHundredTenDD_8559401 : Nat.Prime 8559401 := by norm_num

private theorem prime_oneHundredTenDD_8583139 : Nat.Prime 8583139 := by norm_num

private theorem prime_oneHundredTenDD_9312211 : Nat.Prime 9312211 := by norm_num

private theorem prime_oneHundredTenDD_9324443 : Nat.Prime 9324443 := by norm_num

private theorem prime_oneHundredTenDD_9554807 : Nat.Prime 9554807 := by norm_num

private theorem prime_oneHundredTenDD_10208027 : Nat.Prime 10208027 := by norm_num

private theorem prime_oneHundredTenDD_10686223 : Nat.Prime 10686223 := by norm_num

private theorem prime_oneHundredTenDD_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTenDD_11352647 : Nat.Prime 11352647 := by norm_num

private theorem prime_oneHundredTenDD_12690113 : Nat.Prime 12690113 := by norm_num

private theorem prime_oneHundredTenDD_12696449 : Nat.Prime 12696449 := by norm_num

private theorem prime_oneHundredTenDD_13020991 : Nat.Prime 13020991 := by norm_num

private theorem prime_oneHundredTenDD_13151923 : Nat.Prime 13151923 := by norm_num

private theorem prime_oneHundredTenDD_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredTenDD_14078959 : Nat.Prime 14078959 := by norm_num

private theorem prime_oneHundredTenDD_14213237 : Nat.Prime 14213237 := by norm_num

private theorem prime_oneHundredTenDD_15022199 : Nat.Prime 15022199 := by norm_num

private theorem prime_oneHundredTenDD_16356083 : Nat.Prime 16356083 := by norm_num

private theorem prime_oneHundredTenDD_18226079 : Nat.Prime 18226079 := by norm_num

private theorem prime_oneHundredTenDD_19976597 : Nat.Prime 19976597 := by norm_num

private theorem prime_oneHundredTenDD_20319371 : Nat.Prime 20319371 := by norm_num

private theorem prime_oneHundredTenDD_23118001 : Nat.Prime 23118001 := by norm_num

private theorem prime_oneHundredTenDD_26112773 : Nat.Prime 26112773 := by norm_num

private theorem prime_oneHundredTenDD_27606197 : Nat.Prime 27606197 := by norm_num

private theorem prime_oneHundredTenDD_28936619 : Nat.Prime 28936619 := by norm_num

private theorem prime_oneHundredTenDD_30520993 : Nat.Prime 30520993 := by
  apply lucas_primality 30520993 (7 : ZMod 30520993)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (19, 1), (29, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (19, 1), (29, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) = 30520993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_29
      · exact prime_oneHundredTenDD_577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 30520993) ^ 15260496 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 10173664 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 1606368 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 1052448 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 52896 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_30612443 : Nat.Prime 30612443 := by
  apply lucas_primality 30612443 (2 : ZMod 30612443)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) = 30612443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_2186603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30612443) ^ 15306221 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 4373206 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 14 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_36526547 : Nat.Prime 36526547 := by
  apply lucas_primality 36526547 (2 : ZMod 36526547)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) = 36526547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_44221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36526547) ^ 18263273 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36526547) ^ 5218078 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36526547) ^ 619094 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 36526547) ^ 826 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_37748287 : Nat.Prime 37748287 := by
  apply lucas_primality 37748287 (3 : ZMod 37748287)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (29537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (29537, 1)] : List FactorBlock).map factorBlockValue).prod) = 37748287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_29537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37748287) ^ 18874143 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37748287) ^ 12582762 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37748287) ^ 531666 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 37748287) ^ 1278 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_38002823 : Nat.Prime 38002823 := by
  apply lucas_primality 38002823 (5 : ZMod 38002823)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (89, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (89, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 38002823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_89
      · exact prime_oneHundredTenDD_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38002823) ^ 19001411 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38002823) ^ 3454802 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38002823) ^ 2923294 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38002823) ^ 426998 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 38002823) ^ 25454 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_39350639 : Nat.Prime 39350639 := by
  apply lucas_primality 39350639 (11 : ZMod 39350639)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (221071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (221071, 1)] : List FactorBlock).map factorBlockValue).prod) = 39350639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_89
      · exact prime_oneHundredTenDD_221071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 39350639) ^ 19675319 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 39350639) ^ 442142 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 39350639) ^ 178 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_39669577 : Nat.Prime 39669577 := by
  apply lucas_primality 39669577 (5 : ZMod 39669577)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1652899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1652899, 1)] : List FactorBlock).map factorBlockValue).prod) = 39669577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_1652899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 39669577) ^ 19834788 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 39669577) ^ 13223192 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 39669577) ^ 24 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_42187207 : Nat.Prime 42187207 := by
  apply lucas_primality 42187207 (3 : ZMod 42187207)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (167, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (167, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 42187207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_167
      · exact prime_oneHundredTenDD_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42187207) ^ 21093603 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42187207) ^ 14062402 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42187207) ^ 594186 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42187207) ^ 252618 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 42187207) ^ 71142 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_42689459 : Nat.Prime 42689459 := by
  apply lucas_primality 42689459 (2 : ZMod 42689459)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1297, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1297, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) = 42689459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_1297
      · exact prime_oneHundredTenDD_2351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42689459) ^ 21344729 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42689459) ^ 6098494 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42689459) ^ 32914 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 42689459) ^ 18158 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_43001837 : Nat.Prime 43001837 := by
  apply lucas_primality 43001837 (2 : ZMod 43001837)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) = 43001837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_239
      · exact prime_oneHundredTenDD_1451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43001837) ^ 21500918 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 1387156 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 179924 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 29636 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_43468861 : Nat.Prime 43468861 := by
  apply lucas_primality 43468861 (2 : ZMod 43468861)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (724481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (724481, 1)] : List FactorBlock).map factorBlockValue).prod) = 43468861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_724481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43468861) ^ 21734430 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43468861) ^ 14489620 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43468861) ^ 8693772 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 43468861) ^ 60 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_45149417 : Nat.Prime 45149417 := by
  apply lucas_primality 45149417 (3 : ZMod 45149417)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (17, 1), (25537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (17, 1), (25537, 1)] : List FactorBlock).map factorBlockValue).prod) = 45149417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_25537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45149417) ^ 22574708 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 45149417) ^ 3473032 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 45149417) ^ 2655848 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 45149417) ^ 1768 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_47024249 : Nat.Prime 47024249 := by
  apply lucas_primality 47024249 (3 : ZMod 47024249)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1277, 1), (4603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1277, 1), (4603, 1)] : List FactorBlock).map factorBlockValue).prod) = 47024249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1277
      · exact prime_oneHundredTenDD_4603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47024249) ^ 23512124 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 47024249) ^ 36824 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 47024249) ^ 10216 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_48503657 : Nat.Prime 48503657 := by
  apply lucas_primality 48503657 (3 : ZMod 48503657)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 48503657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48503657) ^ 24251828 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 2552824 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1183016 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1127992 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 267976 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_49471423 : Nat.Prime 49471423 := by
  apply lucas_primality 49471423 (3 : ZMod 49471423)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) = 49471423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_8237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49471423) ^ 24735711 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 16490474 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 7067346 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 4497402 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 3805494 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 6006 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_51923327 : Nat.Prime 51923327 := by
  apply lucas_primality 51923327 (7 : ZMod 51923327)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) = 51923327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_9203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51923327) ^ 25961663 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 7417618 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 3994102 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 1674946 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 5642 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_59892211 : Nat.Prime 59892211 := by
  apply lucas_primality 59892211 (13 : ZMod 59892211)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (7, 2), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (7, 2), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 59892211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 59892211) ^ 29946105 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 59892211) ^ 19964070 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 59892211) ^ 11978442 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 59892211) ^ 8556030 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 59892211) ^ 119070 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1811
      · exact prime_oneHundredTenDD_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_68769247 : Nat.Prime 68769247 := by
  apply lucas_primality 68769247 (3 : ZMod 68769247)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (13, 1), (19, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (13, 1), (19, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 68769247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68769247) ^ 34384623 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 22923082 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 9824178 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 5289942 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 3619434 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 72618 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_77414837 : Nat.Prime 77414837 := by
  apply lucas_primality 77414837 (2 : ZMod 77414837)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1873, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1873, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) = 77414837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1873
      · exact prime_oneHundredTenDD_10333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 77414837) ^ 38707418 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 77414837) ^ 41332 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 77414837) ^ 7492 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_81949669 : Nat.Prime 81949669 := by
  apply lucas_primality 81949669 (2 : ZMod 81949669)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6829139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6829139, 1)] : List FactorBlock).map factorBlockValue).prod) = 81949669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_6829139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 81949669) ^ 40974834 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81949669) ^ 27316556 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 81949669) ^ 12 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_84308839 : Nat.Prime 84308839 := by
  apply lucas_primality 84308839 (3 : ZMod 84308839)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1097, 1), (12809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1097, 1), (12809, 1)] : List FactorBlock).map factorBlockValue).prod) = 84308839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_1097
      · exact prime_oneHundredTenDD_12809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 84308839) ^ 42154419 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 84308839) ^ 28102946 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 84308839) ^ 76854 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 84308839) ^ 6582 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_88812211 : Nat.Prime 88812211 := by
  apply lucas_primality 88812211 (3 : ZMod 88812211)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 88812211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_29
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_37
      · exact prime_oneHundredTenDD_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88812211) ^ 44406105 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 29604070 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 17762442 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 3062490 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2864910 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2400330 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 997890 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_93492409 : Nat.Prime 93492409 := by
  apply lucas_primality 93492409 (7 : ZMod 93492409)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (521, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (521, 1), (7477, 1)] : List FactorBlock).map factorBlockValue).prod) = 93492409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_521
      · exact prime_oneHundredTenDD_7477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 93492409) ^ 46746204 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 93492409) ^ 31164136 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 93492409) ^ 179448 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 93492409) ^ 12504 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_93947437 : Nat.Prime 93947437 := by
  apply lucas_primality 93947437 (5 : ZMod 93947437)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (131, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (131, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) = 93947437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_131
      · exact prime_oneHundredTenDD_1811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 93947437) ^ 46973718 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 31315812 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 8540676 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 717156 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 51876 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_94480049 : Nat.Prime 94480049 := by
  apply lucas_primality 94480049 (3 : ZMod 94480049)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (454231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (454231, 1)] : List FactorBlock).map factorBlockValue).prod) = 94480049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_454231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94480049) ^ 47240024 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 94480049) ^ 7267696 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 94480049) ^ 208 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_95656009 : Nat.Prime 95656009 := by
  apply lucas_primality 95656009 (19 : ZMod 95656009)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (33493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (33493, 1)] : List FactorBlock).map factorBlockValue).prod) = 95656009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_33493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 95656009) ^ 47828004 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 31885336 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 13665144 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 5626824 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 2856 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_95989847 : Nat.Prime 95989847 := by
  apply lucas_primality 95989847 (5 : ZMod 95989847)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (409, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (409, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) = 95989847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_409
      · exact prime_oneHundredTenDD_2729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 95989847) ^ 47994923 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 95989847) ^ 2232322 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 95989847) ^ 234694 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 95989847) ^ 35174 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_100277257 : Nat.Prime 100277257 := by
  apply lucas_primality 100277257 (5 : ZMod 100277257)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4178219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4178219, 1)] : List FactorBlock).map factorBlockValue).prod) = 100277257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_4178219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 100277257) ^ 50138628 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100277257) ^ 33425752 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100277257) ^ 24 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_100878469 : Nat.Prime 100878469 := by
  apply lucas_primality 100878469 (6 : ZMod 100878469)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8406539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8406539, 1)] : List FactorBlock).map factorBlockValue).prod) = 100878469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_8406539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 100878469) ^ 50439234 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 100878469) ^ 33626156 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 100878469) ^ 12 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_105709753 : Nat.Prime 105709753 := by
  apply lucas_primality 105709753 (5 : ZMod 105709753)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (31, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (31, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod) = 105709753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_15787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 105709753) ^ 52854876 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 105709753) ^ 35236584 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 105709753) ^ 3409992 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 105709753) ^ 6696 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_117176551 : Nat.Prime 117176551 := by
  apply lucas_primality 117176551 (3 : ZMod 117176551)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (127, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (127, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) = 117176551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_127
      · exact prime_oneHundredTenDD_6151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 117176551) ^ 58588275 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 39058850 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 23435310 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 922650 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 19050 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_117238469 : Nat.Prime 117238469 := by
  apply lucas_primality 117238469 (2 : ZMod 117238469)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (97, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (97, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) = 117238469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_97
      · exact prime_oneHundredTenDD_7027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 117238469) ^ 58619234 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 2726476 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 1208644 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 16684 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_122791657 : Nat.Prime 122791657 := by
  apply lucas_primality 122791657 (5 : ZMod 122791657)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (103, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (103, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) = 122791657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_103
      · exact prime_oneHundredTenDD_3821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122791657) ^ 61395828 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 40930552 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 9445512 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 1192152 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 32136 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_127396193 : Nat.Prime 127396193 := by
  apply lucas_primality 127396193 (3 : ZMod 127396193)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (11, 1), (149, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (11, 1), (149, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 127396193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_149
      · exact prime_oneHundredTenDD_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 127396193) ^ 63698096 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127396193) ^ 18199456 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127396193) ^ 11581472 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127396193) ^ 855008 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127396193) ^ 367136 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_129532237 : Nat.Prime 129532237 := by
  apply lucas_primality 129532237 (2 : ZMod 129532237)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2803, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2803, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod) = 129532237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_2803
      · exact prime_oneHundredTenDD_3851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 129532237) ^ 64766118 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 129532237) ^ 43177412 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 129532237) ^ 46212 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 129532237) ^ 33636 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_143762009 : Nat.Prime 143762009 := by
  apply lucas_primality 143762009 (3 : ZMod 143762009)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (1382327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (1382327, 1)] : List FactorBlock).map factorBlockValue).prod) = 143762009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_1382327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 143762009) ^ 71881004 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 143762009) ^ 11058616 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 143762009) ^ 104 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_144961759 : Nat.Prime 144961759 := by
  apply lucas_primality 144961759 (3 : ZMod 144961759)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2684477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2684477, 1)] : List FactorBlock).map factorBlockValue).prod) = 144961759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_2684477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 144961759) ^ 72480879 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 144961759) ^ 48320586 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 144961759) ^ 54 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_170937883 : Nat.Prime 170937883 := by
  apply lucas_primality 170937883 (2 : ZMod 170937883)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1367, 1), (6947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1367, 1), (6947, 1)] : List FactorBlock).map factorBlockValue).prod) = 170937883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_1367
      · exact prime_oneHundredTenDD_6947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 170937883) ^ 85468941 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 170937883) ^ 56979294 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 170937883) ^ 125046 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 170937883) ^ 24606 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_188960099 : Nat.Prime 188960099 := by
  apply lucas_primality 188960099 (2 : ZMod 188960099)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (94480049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (94480049, 1)] : List FactorBlock).map factorBlockValue).prod) = 188960099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_94480049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 188960099) ^ 94480049 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 188960099) ^ 2 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_200272519 : Nat.Prime 200272519 := by
  apply lucas_primality 200272519 (15 : ZMod 200272519)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) = 200272519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_181
      · exact prime_oneHundredTenDD_61471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 200272519) ^ 100136259 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 66757506 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 1106478 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 3258 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_208088557 : Nat.Prime 208088557 := by
  apply lucas_primality 208088557 (2 : ZMod 208088557)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1333901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1333901, 1)] : List FactorBlock).map factorBlockValue).prod) = 208088557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_1333901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 208088557) ^ 104044278 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 208088557) ^ 69362852 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 208088557) ^ 16006812 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 208088557) ^ 156 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_210430769 : Nat.Prime 210430769 := by
  apply lucas_primality 210430769 (3 : ZMod 210430769)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) = 210430769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_13151923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 210430769) ^ 105215384 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 210430769) ^ 16 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_211275487 : Nat.Prime 211275487 := by
  apply lucas_primality 211275487 (3 : ZMod 211275487)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3912509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3912509, 1)] : List FactorBlock).map factorBlockValue).prod) = 211275487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_3912509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 211275487) ^ 105637743 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 211275487) ^ 70425162 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 211275487) ^ 54 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_228796471 : Nat.Prime 228796471 := by
  apply lucas_primality 228796471 (6 : ZMod 228796471)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (47, 1), (7727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (47, 1), (7727, 1)] : List FactorBlock).map factorBlockValue).prod) = 228796471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_47
      · exact prime_oneHundredTenDD_7727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 228796471) ^ 114398235 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 228796471) ^ 76265490 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 228796471) ^ 45759294 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 228796471) ^ 32685210 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 228796471) ^ 4868010 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 228796471) ^ 29610 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_230845841 : Nat.Prime 230845841 := by
  apply lucas_primality 230845841 (3 : ZMod 230845841)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (31, 1), (93083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (31, 1), (93083, 1)] : List FactorBlock).map factorBlockValue).prod) = 230845841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_93083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 230845841) ^ 115422920 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 230845841) ^ 46169168 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 230845841) ^ 7446640 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 230845841) ^ 2480 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_256130429 : Nat.Prime 256130429 := by
  apply lucas_primality 256130429 (2 : ZMod 256130429)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (73, 1), (151, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (73, 1), (151, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 256130429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_37
      · exact prime_oneHundredTenDD_73
      · exact prime_oneHundredTenDD_151
      · exact prime_oneHundredTenDD_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256130429) ^ 128065214 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256130429) ^ 6922444 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256130429) ^ 3508636 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256130429) ^ 1696228 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 256130429) ^ 1631404 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_301907911 : Nat.Prime 301907911 := by
  apply lucas_primality 301907911 (15 : ZMod 301907911)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 2), (61, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 2), (61, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 301907911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_61
      · exact prime_oneHundredTenDD_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 301907911) ^ 150953955 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 100635970 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 60381582 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 15889890 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 4949310 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 660630 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_320063083 : Nat.Prime 320063083 := by
  apply lucas_primality 320063083 (2 : ZMod 320063083)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (59, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (59, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) = 320063083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_29
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_31177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 320063083) ^ 160031541 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 106687694 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 11036658 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 5424798 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 10266 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_320471353 : Nat.Prime 320471353 := by
  apply lucas_primality 320471353 (14 : ZMod 320471353)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (261823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (261823, 1)] : List FactorBlock).map factorBlockValue).prod) = 320471353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_261823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 320471353) ^ 160235676 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (14 : ZMod 320471353) ^ 106823784 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (14 : ZMod 320471353) ^ 18851256 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (14 : ZMod 320471353) ^ 1224 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_327798677 : Nat.Prime 327798677 := by
  apply lucas_primality 327798677 (2 : ZMod 327798677)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (81949669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (81949669, 1)] : List FactorBlock).map factorBlockValue).prod) = 327798677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_81949669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 327798677) ^ 163899338 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 327798677) ^ 4 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_340058183 : Nat.Prime 340058183 := by
  apply lucas_primality 340058183 (5 : ZMod 340058183)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (59, 1), (70289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (59, 1), (70289, 1)] : List FactorBlock).map factorBlockValue).prod) = 340058183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_70289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 340058183) ^ 170029091 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 8294102 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 5763698 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 4838 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_355354249 : Nat.Prime 355354249 := by
  apply lucas_primality 355354249 (11 : ZMod 355354249)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (811, 1), (18257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (811, 1), (18257, 1)] : List FactorBlock).map factorBlockValue).prod) = 355354249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_811
      · exact prime_oneHundredTenDD_18257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 355354249) ^ 177677124 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 355354249) ^ 118451416 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 355354249) ^ 438168 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 355354249) ^ 19464 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_12539
      · exact prime_oneHundredTenDD_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_376010941 : Nat.Prime 376010941 := by
  apply lucas_primality 376010941 (2 : ZMod 376010941)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6266849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6266849, 1)] : List FactorBlock).map factorBlockValue).prod) = 376010941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_6266849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376010941) ^ 188005470 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 376010941) ^ 125336980 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 376010941) ^ 75202188 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 376010941) ^ 60 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_381600983 : Nat.Prime 381600983 := by
  apply lucas_primality 381600983 (5 : ZMod 381600983)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3373, 1), (8081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3373, 1), (8081, 1)] : List FactorBlock).map factorBlockValue).prod) = 381600983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_3373
      · exact prime_oneHundredTenDD_8081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 381600983) ^ 190800491 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 381600983) ^ 54514426 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 381600983) ^ 113134 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 381600983) ^ 47222 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_412983787 : Nat.Prime 412983787 := by
  apply lucas_primality 412983787 (2 : ZMod 412983787)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (1128371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (1128371, 1)] : List FactorBlock).map factorBlockValue).prod) = 412983787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_61
      · exact prime_oneHundredTenDD_1128371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 412983787) ^ 206491893 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 412983787) ^ 137661262 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 412983787) ^ 6770226 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 412983787) ^ 366 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_465329339 : Nat.Prime 465329339 := by
  apply lucas_primality 465329339 (6 : ZMod 465329339)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (67, 1), (359, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (67, 1), (359, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 465329339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_67
      · exact prime_oneHundredTenDD_359
      · exact prime_oneHundredTenDD_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 465329339) ^ 232664669 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 465329339) ^ 27372314 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 465329339) ^ 6945214 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 465329339) ^ 1296182 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 465329339) ^ 817802 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_17203
      · exact prime_oneHundredTenDD_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_729919451 : Nat.Prime 729919451 := by
  apply lucas_primality 729919451 (2 : ZMod 729919451)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 2), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 2), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) = 729919451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_86381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 729919451) ^ 364959725 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 145983890 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 56147650 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 8450 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_915701519 : Nat.Prime 915701519 := by
  apply lucas_primality 915701519 (13 : ZMod 915701519)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (4445153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (4445153, 1)] : List FactorBlock).map factorBlockValue).prod) = 915701519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_103
      · exact prime_oneHundredTenDD_4445153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 915701519) ^ 457850759 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 915701519) ^ 8890306 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 915701519) ^ 206 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_919300049 : Nat.Prime 919300049 := by
  apply lucas_primality 919300049 (3 : ZMod 919300049)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (71, 1), (809243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (71, 1), (809243, 1)] : List FactorBlock).map factorBlockValue).prod) = 919300049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_809243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 919300049) ^ 459650024 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 919300049) ^ 12947888 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 919300049) ^ 1136 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1063340107 : Nat.Prime 1063340107 := by
  apply lucas_primality 1063340107 (2 : ZMod 1063340107)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (107, 1), (97429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (107, 1), (97429, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063340107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_107
      · exact prime_oneHundredTenDD_97429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1063340107) ^ 531670053 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063340107) ^ 354446702 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063340107) ^ 62549418 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063340107) ^ 9937758 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063340107) ^ 10914 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1076762003 : Nat.Prime 1076762003 := by
  apply lucas_primality 1076762003 (2 : ZMod 1076762003)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (443, 1), (17117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (443, 1), (17117, 1)] : List FactorBlock).map factorBlockValue).prod) = 1076762003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_443
      · exact prime_oneHundredTenDD_17117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1076762003) ^ 538381001 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1076762003) ^ 15165662 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1076762003) ^ 2430614 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1076762003) ^ 62906 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1113212533 : Nat.Prime 1113212533 := by
  apply lucas_primality 1113212533 (2 : ZMod 1113212533)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (373, 1), (248707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (373, 1), (248707, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113212533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_373
      · exact prime_oneHundredTenDD_248707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1113212533) ^ 556606266 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113212533) ^ 371070844 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113212533) ^ 2984484 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113212533) ^ 4476 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1118289247 : Nat.Prime 1118289247 := by
  apply lucas_primality 1118289247 (3 : ZMod 1118289247)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6203, 1), (30047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6203, 1), (30047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1118289247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_6203
      · exact prime_oneHundredTenDD_30047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1118289247) ^ 559144623 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118289247) ^ 372763082 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118289247) ^ 180282 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118289247) ^ 37218 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1236485539 : Nat.Prime 1236485539 := by
  apply lucas_primality 1236485539 (7 : ZMod 1236485539)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (653, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (653, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1236485539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_653
      · exact prime_oneHundredTenDD_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1236485539) ^ 618242769 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1236485539) ^ 412161846 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1236485539) ^ 20957382 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1236485539) ^ 1893546 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 1236485539) ^ 693486 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1393023833 : Nat.Prime 1393023833 := by
  apply lucas_primality 1393023833 (3 : ZMod 1393023833)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1373, 1), (126823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1373, 1), (126823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1393023833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1373
      · exact prime_oneHundredTenDD_126823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1393023833) ^ 696511916 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1393023833) ^ 1014584 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1393023833) ^ 10984 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1622199443 : Nat.Prime 1622199443 := by
  apply lucas_primality 1622199443 (2 : ZMod 1622199443)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (42689459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (42689459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1622199443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_42689459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1622199443) ^ 811099721 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1622199443) ^ 85378918 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1622199443) ^ 38 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1631470259 : Nat.Prime 1631470259 := by
  apply lucas_primality 1631470259 (2 : ZMod 1631470259)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (523, 1), (141793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (523, 1), (141793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631470259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_523
      · exact prime_oneHundredTenDD_141793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1631470259) ^ 815735129 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 148315478 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 3119446 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 11506 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1750801123 : Nat.Prime 1750801123 := by
  apply lucas_primality 1750801123 (3 : ZMod 1750801123)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (4631749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (4631749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1750801123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_4631749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1750801123) ^ 875400561 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 583600374 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 250114446 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 378 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2153283367 : Nat.Prime 2153283367 := by
  apply lucas_primality 2153283367 (6 : ZMod 2153283367)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (27606197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (27606197, 1)] : List FactorBlock).map factorBlockValue).prod) = 2153283367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_27606197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2153283367) ^ 1076641683 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2153283367) ^ 717761122 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2153283367) ^ 165637182 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 2153283367) ^ 78 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2253419027 : Nat.Prime 2253419027 := by
  apply lucas_primality 2253419027 (2 : ZMod 2253419027)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2063, 1), (546151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2063, 1), (546151, 1)] : List FactorBlock).map factorBlockValue).prod) = 2253419027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_2063
      · exact prime_oneHundredTenDD_546151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2253419027) ^ 1126709513 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2253419027) ^ 1092302 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2253419027) ^ 4126 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2267521189 : Nat.Prime 2267521189 := by
  apply lucas_primality 2267521189 (2 : ZMod 2267521189)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (188960099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (188960099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267521189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_188960099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2267521189) ^ 1133760594 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267521189) ^ 755840396 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267521189) ^ 12 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2358036103 : Nat.Prime 2358036103 := by
  apply lucas_primality 2358036103 (3 : ZMod 2358036103)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23118001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23118001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2358036103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_23118001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2358036103) ^ 1179018051 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2358036103) ^ 786012034 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2358036103) ^ 138708006 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2358036103) ^ 102 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2520804151 : Nat.Prime 2520804151 := by
  apply lucas_primality 2520804151 (15 : ZMod 2520804151)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (5601787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (5601787, 1)] : List FactorBlock).map factorBlockValue).prod) = 2520804151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_5601787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 2520804151) ^ 1260402075 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 2520804151) ^ 840268050 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 2520804151) ^ 504160830 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (15 : ZMod 2520804151) ^ 450 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2688712237 : Nat.Prime 2688712237 := by
  apply lucas_primality 2688712237 (2 : ZMod 2688712237)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (23, 1), (463891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (23, 1), (463891, 1)] : List FactorBlock).map factorBlockValue).prod) = 2688712237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_463891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2688712237) ^ 1344356118 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2688712237) ^ 896237412 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2688712237) ^ 384101748 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2688712237) ^ 116900532 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2688712237) ^ 5796 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_3112739761 : Nat.Prime 3112739761 := by
  apply lucas_primality 3112739761 (7 : ZMod 3112739761)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (31, 1), (32183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (31, 1), (32183, 1)] : List FactorBlock).map factorBlockValue).prod) = 3112739761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_32183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3112739761) ^ 1556369880 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3112739761) ^ 1037579920 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3112739761) ^ 622547952 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3112739761) ^ 239441520 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3112739761) ^ 100410960 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3112739761) ^ 96720 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_3204713531 : Nat.Prime 3204713531 := by
  apply lucas_primality 3204713531 (2 : ZMod 3204713531)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (320471353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (320471353, 1)] : List FactorBlock).map factorBlockValue).prod) = 3204713531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_320471353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3204713531) ^ 1602356765 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3204713531) ^ 640942706 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 3204713531) ^ 10 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_3262940519 : Nat.Prime 3262940519 := by
  apply lucas_primality 3262940519 (11 : ZMod 3262940519)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1631470259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1631470259, 1)] : List FactorBlock).map factorBlockValue).prod) = 3262940519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1631470259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 3262940519) ^ 1631470259 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3262940519) ^ 2 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_4171314503 : Nat.Prime 4171314503 := by
  apply lucas_primality 4171314503 (5 : ZMod 4171314503)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_48503657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4171314503) ^ 2085657251 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 97007314 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 86 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_4210504841 : Nat.Prime 4210504841 := by
  apply lucas_primality 4210504841 (3 : ZMod 4210504841)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (41, 1), (1229, 1), (2089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (41, 1), (1229, 1), (2089, 1)] : List FactorBlock).map factorBlockValue).prod) = 4210504841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_1229
      · exact prime_oneHundredTenDD_2089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4210504841) ^ 2105252420 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 842100968 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 102695240 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 3425960 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 2015560 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_4914242863 : Nat.Prime 4914242863 := by
  apply lucas_primality 4914242863 (3 : ZMod 4914242863)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) = 4914242863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_19976597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4914242863) ^ 2457121431 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 1638080954 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 119859582 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 246 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_5121009329 : Nat.Prime 5121009329 := by
  apply lucas_primality 5121009329 (3 : ZMod 5121009329)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (320063083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (320063083, 1)] : List FactorBlock).map factorBlockValue).prod) = 5121009329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_320063083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5121009329) ^ 2560504664 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5121009329) ^ 16 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_5429792839 : Nat.Prime 5429792839 := by
  apply lucas_primality 5429792839 (6 : ZMod 5429792839)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5429792839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_709
      · exact prime_oneHundredTenDD_1276397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5429792839) ^ 2714896419 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 1809930946 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 7658382 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 4254 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_5839355609 : Nat.Prime 5839355609 := by
  apply lucas_primality 5839355609 (3 : ZMod 5839355609)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (729919451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (729919451, 1)] : List FactorBlock).map factorBlockValue).prod) = 5839355609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_729919451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5839355609) ^ 2919677804 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5839355609) ^ 8 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_7137860761 : Nat.Prime 7137860761 := by
  apply lucas_primality 7137860761 (7 : ZMod 7137860761)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (449, 1), (44159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (449, 1), (44159, 1)] : List FactorBlock).map factorBlockValue).prod) = 7137860761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_449
      · exact prime_oneHundredTenDD_44159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7137860761) ^ 3568930380 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 2379286920 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 1427572152 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 15897240 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 161640 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_7339440673 : Nat.Prime 7339440673 := by
  apply lucas_primality 7339440673 (5 : ZMod 7339440673)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (2003, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (2003, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 7339440673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_2003
      · exact prime_oneHundredTenDD_4241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7339440673) ^ 3669720336 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339440673) ^ 2446480224 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339440673) ^ 3664224 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339440673) ^ 1730592 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_7537219631 : Nat.Prime 7537219631 := by
  apply lucas_primality 7537219631 (7 : ZMod 7537219631)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (39669577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (39669577, 1)] : List FactorBlock).map factorBlockValue).prod) = 7537219631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_39669577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7537219631) ^ 3768609815 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 7537219631) ^ 1507443926 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 7537219631) ^ 396695770 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 7537219631) ^ 190 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8726927519 : Nat.Prime 8726927519 := by
  apply lucas_primality 8726927519 (7 : ZMod 8726927519)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (14213237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (14213237, 1)] : List FactorBlock).map factorBlockValue).prod) = 8726927519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_307
      · exact prime_oneHundredTenDD_14213237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8726927519) ^ 4363463759 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8726927519) ^ 28426474 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8726927519) ^ 614 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_11952595463 : Nat.Prime 11952595463 := by
  apply lucas_primality 11952595463 (5 : ZMod 11952595463)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4057, 1), (1473083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4057, 1), (1473083, 1)] : List FactorBlock).map factorBlockValue).prod) = 11952595463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_4057
      · exact prime_oneHundredTenDD_1473083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11952595463) ^ 5976297731 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11952595463) ^ 2946166 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11952595463) ^ 8114 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_14321340013 : Nat.Prime 14321340013 := by
  apply lucas_primality 14321340013 (13 : ZMod 14321340013)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (307, 1), (555349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (307, 1), (555349, 1)] : List FactorBlock).map factorBlockValue).prod) = 14321340013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_307
      · exact prime_oneHundredTenDD_555349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 14321340013) ^ 7160670006 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 14321340013) ^ 4773780004 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 14321340013) ^ 2045905716 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 14321340013) ^ 46649316 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 14321340013) ^ 25788 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_16227481211 : Nat.Prime 16227481211 := by
  apply lucas_primality 16227481211 (2 : ZMod 16227481211)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (389, 1), (461, 1), (9049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (389, 1), (461, 1), (9049, 1)] : List FactorBlock).map factorBlockValue).prod) = 16227481211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_389
      · exact prime_oneHundredTenDD_461
      · exact prime_oneHundredTenDD_9049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16227481211) ^ 8113740605 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16227481211) ^ 3245496242 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16227481211) ^ 41715890 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16227481211) ^ 35200610 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16227481211) ^ 1793290 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_17805412511 : Nat.Prime 17805412511 := by
  apply lucas_primality 17805412511 (19 : ZMod 17805412511)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (77414837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (77414837, 1)] : List FactorBlock).map factorBlockValue).prod) = 17805412511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_77414837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 17805412511) ^ 8902706255 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (19 : ZMod 17805412511) ^ 3561082502 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (19 : ZMod 17805412511) ^ 774148370 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (19 : ZMod 17805412511) ^ 230 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_19358100161 : Nat.Prime 19358100161 := by
  apply lucas_primality 19358100161 (3 : ZMod 19358100161)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (103, 1), (83903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (103, 1), (83903, 1)] : List FactorBlock).map factorBlockValue).prod) = 19358100161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_103
      · exact prime_oneHundredTenDD_83903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19358100161) ^ 9679050080 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 3871620032 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 2765442880 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 187942720 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 230720 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_21238689431 : Nat.Prime 21238689431 := by
  apply lucas_primality 21238689431 (7 : ZMod 21238689431)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (43, 1), (79, 1), (89317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (43, 1), (79, 1), (89317, 1)] : List FactorBlock).map factorBlockValue).prod) = 21238689431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_79
      · exact prime_oneHundredTenDD_89317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21238689431) ^ 10619344715 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 21238689431) ^ 4247737886 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 21238689431) ^ 3034098490 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 21238689431) ^ 493923010 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 21238689431) ^ 268844170 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 21238689431) ^ 237790 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_22622892419 : Nat.Prime 22622892419 := by
  apply lucas_primality 22622892419 (2 : ZMod 22622892419)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (230845841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (230845841, 1)] : List FactorBlock).map factorBlockValue).prod) = 22622892419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_230845841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22622892419) ^ 11311446209 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22622892419) ^ 3231841774 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22622892419) ^ 98 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_23037563281 : Nat.Prime 23037563281 := by
  apply lucas_primality 23037563281 (7 : ZMod 23037563281)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (95989847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (95989847, 1)] : List FactorBlock).map factorBlockValue).prod) = 23037563281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_95989847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23037563281) ^ 11518781640 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 23037563281) ^ 7679187760 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 23037563281) ^ 4607512656 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 23037563281) ^ 240 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_23096547757 : Nat.Prime 23096547757 := by
  apply lucas_primality 23096547757 (5 : ZMod 23096547757)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) = 23096547757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_79
      · exact prime_oneHundredTenDD_163
      · exact prime_oneHundredTenDD_49823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23096547757) ^ 11548273878 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 7698849252 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 292361364 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 141696612 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 463572 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_24822965413 : Nat.Prime 24822965413 := by
  apply lucas_primality 24822965413 (2 : ZMod 24822965413)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (17, 1), (5794343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (17, 1), (5794343, 1)] : List FactorBlock).map factorBlockValue).prod) = 24822965413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_5794343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24822965413) ^ 12411482706 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24822965413) ^ 8274321804 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24822965413) ^ 3546137916 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24822965413) ^ 1460174436 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24822965413) ^ 4284 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_26752207429 : Nat.Prime 26752207429 := by
  apply lucas_primality 26752207429 (2 : ZMod 26752207429)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) = 26752207429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_4621
      · exact prime_oneHundredTenDD_160813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26752207429) ^ 13376103714 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 8917402476 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 5789268 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 166356 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_26896283387 : Nat.Prime 26896283387 := by
  apply lucas_primality 26896283387 (2 : ZMod 26896283387)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) = 26896283387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_37
      · exact prime_oneHundredTenDD_51923327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26896283387) ^ 13448141693 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 3842326198 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 726926578 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 518 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_27918548017 : Nat.Prime 27918548017 := by
  apply lucas_primality 27918548017 (5 : ZMod 27918548017)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) = 27918548017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_30612443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27918548017) ^ 13959274008 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 9306182672 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 1469397264 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 912 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_29485457179 : Nat.Prime 29485457179 := by
  apply lucas_primality 29485457179 (2 : ZMod 29485457179)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) = 29485457179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_4914242863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29485457179) ^ 14742728589 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 9828485726 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 6 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_30352877609 : Nat.Prime 30352877609 := by
  apply lucas_primality 30352877609 (3 : ZMod 30352877609)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (41, 1), (67, 1), (97, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (41, 1), (67, 1), (97, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 30352877609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_29
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_67
      · exact prime_oneHundredTenDD_97
      · exact prime_oneHundredTenDD_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30352877609) ^ 15176438804 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 1046650952 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 740314088 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 453028024 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 312916264 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 61818488 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_33446361583 : Nat.Prime 33446361583 := by
  apply lucas_primality 33446361583 (3 : ZMod 33446361583)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (211, 1), (382883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (211, 1), (382883, 1)] : List FactorBlock).map factorBlockValue).prod) = 33446361583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_211
      · exact prime_oneHundredTenDD_382883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33446361583) ^ 16723180791 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 11148787194 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 1454189634 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 158513562 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 87354 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_37616242861 : Nat.Prime 37616242861 := by
  apply lucas_primality 37616242861 (2 : ZMod 37616242861)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (7, 1), (23, 1), (144223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (7, 1), (23, 1), (144223, 1)] : List FactorBlock).map factorBlockValue).prod) = 37616242861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_144223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37616242861) ^ 18808121430 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 12538747620 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 7523248572 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 5373748980 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 1635488820 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 260820 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_38716200323 : Nat.Prime 38716200323 := by
  apply lucas_primality 38716200323 (2 : ZMod 38716200323)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19358100161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19358100161, 1)] : List FactorBlock).map factorBlockValue).prod) = 38716200323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_19358100161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 38716200323) ^ 19358100161 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38716200323) ^ 2 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_45665306881 : Nat.Prime 45665306881 := by
  apply lucas_primality 45665306881 (14 : ZMod 45665306881)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (113, 1), (105239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (113, 1), (105239, 1)] : List FactorBlock).map factorBlockValue).prod) = 45665306881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_113
      · exact prime_oneHundredTenDD_105239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 45665306881) ^ 22832653440 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 15221768960 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 9133061376 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 404117760 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 433920 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_56101637827 : Nat.Prime 56101637827 := by
  apply lucas_primality 56101637827 (5 : ZMod 56101637827)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 2), (67, 1), (91753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 2), (67, 1), (91753, 1)] : List FactorBlock).map factorBlockValue).prod) = 56101637827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_67
      · exact prime_oneHundredTenDD_91753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 56101637827) ^ 28050818913 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 56101637827) ^ 18700545942 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 56101637827) ^ 4315510602 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 56101637827) ^ 837337878 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 56101637827) ^ 611442 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_56645794981 : Nat.Prime 56645794981 := by
  apply lucas_primality 56645794981 (7 : ZMod 56645794981)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (59, 1), (1907, 1), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (59, 1), (1907, 1), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) = 56645794981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_1907
      · exact prime_oneHundredTenDD_2797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56645794981) ^ 28322897490 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 18881931660 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 11329158996 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 960098220 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 29704140 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 20252340 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_57285360053 : Nat.Prime 57285360053 := by
  apply lucas_primality 57285360053 (2 : ZMod 57285360053)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14321340013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14321340013, 1)] : List FactorBlock).map factorBlockValue).prod) = 57285360053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_14321340013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 57285360053) ^ 28642680026 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 57285360053) ^ 4 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_62053524251 : Nat.Prime 62053524251 := by
  apply lucas_primality 62053524251 (2 : ZMod 62053524251)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (47, 1), (5281151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (47, 1), (5281151, 1)] : List FactorBlock).map factorBlockValue).prod) = 62053524251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_47
      · exact prime_oneHundredTenDD_5281151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62053524251) ^ 31026762125 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 62053524251) ^ 12410704850 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 62053524251) ^ 1320287750 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 62053524251) ^ 11750 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_64002540631 : Nat.Prime 64002540631 := by
  apply lucas_primality 64002540631 (3 : ZMod 64002540631)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (89, 1), (180233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (89, 1), (180233, 1)] : List FactorBlock).map factorBlockValue).prod) = 64002540631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_89
      · exact prime_oneHundredTenDD_180233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64002540631) ^ 32001270315 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 21334180210 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 12800508126 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 9143220090 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 3368554770 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 719129670 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 355110 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_67576283399 : Nat.Prime 67576283399 := by
  apply lucas_primality 67576283399 (7 : ZMod 67576283399)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (9013, 1), (16963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (9013, 1), (16963, 1)] : List FactorBlock).map factorBlockValue).prod) = 67576283399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_9013
      · exact prime_oneHundredTenDD_16963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 67576283399) ^ 33788141699 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 67576283399) ^ 5198175646 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 67576283399) ^ 3975075494 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 67576283399) ^ 7497646 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 67576283399) ^ 3983746 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_74775919583 : Nat.Prime 74775919583 := by
  apply lucas_primality 74775919583 (5 : ZMod 74775919583)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74775919583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_9554807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74775919583) ^ 37387959791 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 10682274226 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 5751993814 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 1738974874 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 7826 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_83162934731 : Nat.Prime 83162934731 := by
  apply lucas_primality 83162934731 (2 : ZMod 83162934731)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (239, 1), (5657, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (239, 1), (5657, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) = 83162934731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_239
      · exact prime_oneHundredTenDD_5657
      · exact prime_oneHundredTenDD_6151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83162934731) ^ 41581467365 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 83162934731) ^ 16632586946 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 83162934731) ^ 347962070 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 83162934731) ^ 14700890 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 83162934731) ^ 13520230 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_127220573119 : Nat.Prime 127220573119 := by
  apply lucas_primality 127220573119 (3 : ZMod 127220573119)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (71, 1), (2953, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (71, 1), (2953, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 127220573119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_2953
      · exact prime_oneHundredTenDD_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 127220573119) ^ 63610286559 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127220573119) ^ 42406857706 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127220573119) ^ 5531329266 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127220573119) ^ 1791839058 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127220573119) ^ 43081806 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127220573119) ^ 28933494 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_127250986903 : Nat.Prime 127250986903 := by
  apply lucas_primality 127250986903 (3 : ZMod 127250986903)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (38317, 1), (42577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (38317, 1), (42577, 1)] : List FactorBlock).map factorBlockValue).prod) = 127250986903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_38317
      · exact prime_oneHundredTenDD_42577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 127250986903) ^ 63625493451 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127250986903) ^ 42416995634 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127250986903) ^ 9788537454 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127250986903) ^ 3321006 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 127250986903) ^ 2988726 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_135152566799 : Nat.Prime 135152566799 := by
  apply lucas_primality 135152566799 (17 : ZMod 135152566799)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67576283399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67576283399, 1)] : List FactorBlock).map factorBlockValue).prod) = 135152566799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_67576283399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 135152566799) ^ 67576283399 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 135152566799) ^ 2 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_136773649087 : Nat.Prime 136773649087 := by
  apply lucas_primality 136773649087 (6 : ZMod 136773649087)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (256130429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (256130429, 1)] : List FactorBlock).map factorBlockValue).prod) = 136773649087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_89
      · exact prime_oneHundredTenDD_256130429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 136773649087) ^ 68386824543 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 136773649087) ^ 45591216362 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 136773649087) ^ 1536782574 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 136773649087) ^ 534 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_853
      · exact prime_oneHundredTenDD_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_150249777467 : Nat.Prime 150249777467 := by
  apply lucas_primality 150249777467 (2 : ZMod 150249777467)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (97, 1), (12696449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (97, 1), (12696449, 1)] : List FactorBlock).map factorBlockValue).prod) = 150249777467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_61
      · exact prime_oneHundredTenDD_97
      · exact prime_oneHundredTenDD_12696449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 150249777467) ^ 75124888733 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 150249777467) ^ 2463111106 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 150249777467) ^ 1548966778 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 150249777467) ^ 11834 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_154518491651 : Nat.Prime 154518491651 := by
  apply lucas_primality 154518491651 (2 : ZMod 154518491651)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (37, 1), (2880121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (37, 1), (2880121, 1)] : List FactorBlock).map factorBlockValue).prod) = 154518491651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_29
      · exact prime_oneHundredTenDD_37
      · exact prime_oneHundredTenDD_2880121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 154518491651) ^ 77259245825 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 30903698330 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 5328223850 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 4176175450 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 53650 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_160710694637 : Nat.Prime 160710694637 := by
  apply lucas_primality 160710694637 (2 : ZMod 160710694637)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (151, 1), (8583139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (151, 1), (8583139, 1)] : List FactorBlock).map factorBlockValue).prod) = 160710694637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_151
      · exact prime_oneHundredTenDD_8583139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 160710694637) ^ 80355347318 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 160710694637) ^ 5184215956 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 160710694637) ^ 1064309236 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 160710694637) ^ 18724 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_186461254597 : Nat.Prime 186461254597 := by
  apply lucas_primality 186461254597 (6 : ZMod 186461254597)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (463, 1), (491, 1), (68351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (463, 1), (491, 1), (68351, 1)] : List FactorBlock).map factorBlockValue).prod) = 186461254597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_463
      · exact prime_oneHundredTenDD_491
      · exact prime_oneHundredTenDD_68351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 186461254597) ^ 93230627298 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 62153751532 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 402724092 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 379758156 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 2727996 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_207036943339 : Nat.Prime 207036943339 := by
  apply lucas_primality 207036943339 (7 : ZMod 207036943339)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11863, 1), (2908721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11863, 1), (2908721, 1)] : List FactorBlock).map factorBlockValue).prod) = 207036943339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11863
      · exact prime_oneHundredTenDD_2908721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 207036943339) ^ 103518471669 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 207036943339) ^ 69012314446 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 207036943339) ^ 17452326 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 207036943339) ^ 71178 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_210359508407 : Nat.Prime 210359508407 := by
  apply lucas_primality 210359508407 (5 : ZMod 210359508407)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (859, 1), (6444443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (859, 1), (6444443, 1)] : List FactorBlock).map factorBlockValue).prod) = 210359508407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_859
      · exact prime_oneHundredTenDD_6444443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 210359508407) ^ 105179754203 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 11071553074 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 244888834 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 32642 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_230375632811 : Nat.Prime 230375632811 := by
  apply lucas_primality 230375632811 (6 : ZMod 230375632811)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23037563281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23037563281, 1)] : List FactorBlock).map factorBlockValue).prod) = 230375632811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_23037563281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 230375632811) ^ 115187816405 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 230375632811) ^ 46075126562 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 230375632811) ^ 10 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_279961876619 : Nat.Prime 279961876619 := by
  apply lucas_primality 279961876619 (2 : ZMod 279961876619)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (39343, 1), (114773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (39343, 1), (114773, 1)] : List FactorBlock).map factorBlockValue).prod) = 279961876619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_31
      · exact prime_oneHundredTenDD_39343
      · exact prime_oneHundredTenDD_114773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 279961876619) ^ 139980938309 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 279961876619) ^ 9031028278 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 279961876619) ^ 7115926 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 279961876619) ^ 2439266 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_427597171451 : Nat.Prime 427597171451 := by
  apply lucas_primality 427597171451 (2 : ZMod 427597171451)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (83, 1), (3552947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (83, 1), (3552947, 1)] : List FactorBlock).map factorBlockValue).prod) = 427597171451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_29
      · exact prime_oneHundredTenDD_83
      · exact prime_oneHundredTenDD_3552947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 427597171451) ^ 213798585725 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 427597171451) ^ 85519434290 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 427597171451) ^ 14744730050 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 427597171451) ^ 5151773150 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 427597171451) ^ 120350 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_476907466417 : Nat.Prime 476907466417 := by
  apply lucas_primality 476907466417 (10 : ZMod 476907466417)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) = 476907466417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_73
      · exact prime_oneHundredTenDD_3165203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 476907466417) ^ 238453733208 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 158969155472 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 11090871312 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 6532978992 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 150672 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_538664062567 : Nat.Prime 538664062567 := by
  apply lucas_primality 538664062567 (3 : ZMod 538664062567)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (877, 1), (298451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (877, 1), (298451, 1)] : List FactorBlock).map factorBlockValue).prod) = 538664062567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_877
      · exact prime_oneHundredTenDD_298451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 538664062567) ^ 269332031283 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 179554687522 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 76952008938 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 614212158 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 1804866 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_628773431723 : Nat.Prime 628773431723 := by
  apply lucas_primality 628773431723 (2 : ZMod 628773431723)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (3112739761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (3112739761, 1)] : List FactorBlock).map factorBlockValue).prod) = 628773431723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_101
      · exact prime_oneHundredTenDD_3112739761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 628773431723) ^ 314386715861 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 628773431723) ^ 6225479522 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 628773431723) ^ 202 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_667616203883 : Nat.Prime 667616203883 := by
  apply lucas_primality 667616203883 (2 : ZMod 667616203883)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (239, 1), (37748287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (239, 1), (37748287, 1)] : List FactorBlock).map factorBlockValue).prod) = 667616203883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_37
      · exact prime_oneHundredTenDD_239
      · exact prime_oneHundredTenDD_37748287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 667616203883) ^ 333808101941 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 667616203883) ^ 18043681186 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 667616203883) ^ 2793373238 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 667616203883) ^ 17686 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_700722673081 : Nat.Prime 700722673081 := by
  apply lucas_primality 700722673081 (13 : ZMod 700722673081)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (5839355609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (5839355609, 1)] : List FactorBlock).map factorBlockValue).prod) = 700722673081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_5839355609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 700722673081) ^ 350361336540 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 233574224360 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 140144534616 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 120 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_990099933397 : Nat.Prime 990099933397 := by
  apply lucas_primality 990099933397 (5 : ZMod 990099933397)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1103, 1), (10686223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1103, 1), (10686223, 1)] : List FactorBlock).map factorBlockValue).prod) = 990099933397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_1103
      · exact prime_oneHundredTenDD_10686223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 990099933397) ^ 495049966698 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 990099933397) ^ 330033311132 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 990099933397) ^ 141442847628 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 990099933397) ^ 897642732 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 990099933397) ^ 92652 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1022058768707 : Nat.Prime 1022058768707 := by
  apply lucas_primality 1022058768707 (2 : ZMod 1022058768707)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022058768707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_26896283387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1022058768707) ^ 511029384353 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 53792566774 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 38 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1293320737679 : Nat.Prime 1293320737679 := by
  apply lucas_primality 1293320737679 (11 : ZMod 1293320737679)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (274117, 1), (2359067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (274117, 1), (2359067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1293320737679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_274117
      · exact prime_oneHundredTenDD_2359067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1293320737679) ^ 646660368839 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293320737679) ^ 4718134 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293320737679) ^ 548234 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1295508299753 : Nat.Prime 1295508299753 := by
  apply lucas_primality 1295508299753 (3 : ZMod 1295508299753)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295508299753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_43759
      · exact prime_oneHundredTenDD_3700691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1295508299753) ^ 647754149876 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 29605528 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 350072 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1408055893883 : Nat.Prime 1408055893883 := by
  apply lucas_primality 1408055893883 (5 : ZMod 1408055893883)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (64002540631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (64002540631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408055893883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_64002540631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1408055893883) ^ 704027946941 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408055893883) ^ 128005081262 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408055893883) ^ 22 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1408520993987 : Nat.Prime 1408520993987 := by
  apply lucas_primality 1408520993987 (2 : ZMod 1408520993987)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (109, 1), (340058183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (109, 1), (340058183, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408520993987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_109
      · exact prime_oneHundredTenDD_340058183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1408520993987) ^ 704260496993 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 74132683894 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 12922210954 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 4142 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1554854151563 : Nat.Prime 1554854151563 := by
  apply lucas_primality 1554854151563 (2 : ZMod 1554854151563)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (7013, 1), (289439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (7013, 1), (289439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1554854151563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_383
      · exact prime_oneHundredTenDD_7013
      · exact prime_oneHundredTenDD_289439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1554854151563) ^ 777427075781 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1554854151563) ^ 4059671414 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1554854151563) ^ 221710274 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1554854151563) ^ 5371958 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_4383869460577 : Nat.Prime 4383869460577 := by
  apply lucas_primality 4383869460577 (10 : ZMod 4383869460577)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (45665306881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (45665306881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4383869460577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_45665306881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4383869460577) ^ 2191934730288 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4383869460577) ^ 1461289820192 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (10 : ZMod 4383869460577) ^ 96 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_4542054392287 : Nat.Prime 4542054392287 := by
  apply lucas_primality 4542054392287 (3 : ZMod 4542054392287)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (73, 1), (84308839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (73, 1), (84308839, 1)] : List FactorBlock).map factorBlockValue).prod) = 4542054392287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_73
      · exact prime_oneHundredTenDD_84308839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4542054392287) ^ 2271027196143 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 1514018130762 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 110781814446 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 62219923182 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 53874 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_7214541480163 : Nat.Prime 7214541480163 := by
  apply lucas_primality 7214541480163 (3 : ZMod 7214541480163)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (53, 1), (2520804151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (53, 1), (2520804151, 1)] : List FactorBlock).map factorBlockValue).prod) = 7214541480163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_53
      · exact prime_oneHundredTenDD_2520804151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7214541480163) ^ 3607270740081 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7214541480163) ^ 2404847160054 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7214541480163) ^ 136123424154 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7214541480163) ^ 2862 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8165702670911 : Nat.Prime 8165702670911 := by
  apply lucas_primality 8165702670911 (11 : ZMod 8165702670911)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (281, 1), (170937883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (281, 1), (170937883, 1)] : List FactorBlock).map factorBlockValue).prod) = 8165702670911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_281
      · exact prime_oneHundredTenDD_170937883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8165702670911) ^ 4082851335455 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 8165702670911) ^ 1633140534182 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 8165702670911) ^ 480335451230 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 8165702670911) ^ 29059440110 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 8165702670911) ^ 47770 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8501986179367 : Nat.Prime 8501986179367 := by
  apply lucas_primality 8501986179367 (3 : ZMod 8501986179367)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (4447, 1), (1650991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (4447, 1), (1650991, 1)] : List FactorBlock).map factorBlockValue).prod) = 8501986179367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_193
      · exact prime_oneHundredTenDD_4447
      · exact prime_oneHundredTenDD_1650991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8501986179367) ^ 4250993089683 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8501986179367) ^ 2833995393122 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8501986179367) ^ 44051741862 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8501986179367) ^ 1911847578 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8501986179367) ^ 5149626 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8503336257881 : Nat.Prime 8503336257881 := by
  apply lucas_primality 8503336257881 (3 : ZMod 8503336257881)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (47, 1), (877, 1), (1901, 1), (2713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (47, 1), (877, 1), (1901, 1), (2713, 1)] : List FactorBlock).map factorBlockValue).prod) = 8503336257881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_47
      · exact prime_oneHundredTenDD_877
      · exact prime_oneHundredTenDD_1901
      · exact prime_oneHundredTenDD_2713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8503336257881) ^ 4251668128940 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 1700667251576 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 180922048040 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 9695936440 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 4473085880 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 3134292760 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8503796454319 : Nat.Prime 8503796454319 := by
  apply lucas_primality 8503796454319 (3 : ZMod 8503796454319)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (953, 1), (15022199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (953, 1), (15022199, 1)] : List FactorBlock).map factorBlockValue).prod) = 8503796454319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_953
      · exact prime_oneHundredTenDD_15022199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8503796454319) ^ 4251898227159 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503796454319) ^ 2834598818106 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503796454319) ^ 773072404938 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503796454319) ^ 8923186206 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503796454319) ^ 566082 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8524454832463 : Nat.Prime 8524454832463 := by
  apply lucas_primality 8524454832463 (3 : ZMod 8524454832463)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8524454832463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_74775919583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8524454832463) ^ 4262227416231 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 2841484944154 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 448655517498 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 114 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_9231195796909 : Nat.Prime 9231195796909 := by
  apply lucas_primality 9231195796909 (2 : ZMod 9231195796909)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (33446361583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (33446361583, 1)] : List FactorBlock).map factorBlockValue).prod) = 9231195796909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_33446361583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9231195796909) ^ 4615597898454 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 3077065265636 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 401356338996 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 276 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_10657483763819 : Nat.Prime 10657483763819 := by
  apply lucas_primality 10657483763819 (2 : ZMod 10657483763819)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (347, 1), (1427, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (347, 1), (1427, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) = 10657483763819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_109
      · exact prime_oneHundredTenDD_347
      · exact prime_oneHundredTenDD_1427
      · exact prime_oneHundredTenDD_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10657483763819) ^ 5328741881909 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 97775080402 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 30713209694 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 7468453934 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 107946842 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_11307656677487 : Nat.Prime 11307656677487 := by
  apply lucas_primality 11307656677487 (5 : ZMod 11307656677487)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (193, 1), (2253419027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (193, 1), (2253419027, 1)] : List FactorBlock).map factorBlockValue).prod) = 11307656677487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_193
      · exact prime_oneHundredTenDD_2253419027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11307656677487) ^ 5653828338743 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11307656677487) ^ 869819744422 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11307656677487) ^ 58588894702 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 11307656677487) ^ 5018 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_15331615327909 : Nat.Prime 15331615327909 := by
  apply lucas_primality 15331615327909 (2 : ZMod 15331615327909)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (38716200323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (38716200323, 1)] : List FactorBlock).map factorBlockValue).prod) = 15331615327909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_38716200323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15331615327909) ^ 7665807663954 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15331615327909) ^ 5110538442636 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15331615327909) ^ 1393783211628 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15331615327909) ^ 396 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_15577914241229 : Nat.Prime 15577914241229 := by
  apply lucas_primality 15577914241229 (2 : ZMod 15577914241229)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4253, 1), (915701519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4253, 1), (915701519, 1)] : List FactorBlock).map factorBlockValue).prod) = 15577914241229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_4253
      · exact prime_oneHundredTenDD_915701519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15577914241229) ^ 7788957120614 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15577914241229) ^ 3662806076 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 15577914241229) ^ 17012 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_19456411085651 : Nat.Prime 19456411085651 := by
  apply lucas_primality 19456411085651 (2 : ZMod 19456411085651)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (11, 1), (347, 1), (1171, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (11, 1), (347, 1), (1171, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) = 19456411085651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_347
      · exact prime_oneHundredTenDD_1171
      · exact prime_oneHundredTenDD_12437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19456411085651) ^ 9728205542825 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 3891282217130 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 2779487297950 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 1768764644150 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 56070348950 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 16615210150 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 1564397450 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_21195094540883 : Nat.Prime 21195094540883 := by
  apply lucas_primality 21195094540883 (2 : ZMod 21195094540883)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (2111, 1), (68769247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (2111, 1), (68769247, 1)] : List FactorBlock).map factorBlockValue).prod) = 21195094540883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_73
      · exact prime_oneHundredTenDD_2111
      · exact prime_oneHundredTenDD_68769247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21195094540883) ^ 10597547270441 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 21195094540883) ^ 290343760834 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 21195094540883) ^ 10040310062 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 21195094540883) ^ 308206 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_52383676435451 : Nat.Prime 52383676435451 := by
  apply lucas_primality 52383676435451 (2 : ZMod 52383676435451)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (139, 1), (7537219631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (139, 1), (7537219631, 1)] : List FactorBlock).map factorBlockValue).prod) = 52383676435451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_139
      · exact prime_oneHundredTenDD_7537219631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52383676435451) ^ 26191838217725 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52383676435451) ^ 10476735287090 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52383676435451) ^ 376860981550 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 52383676435451) ^ 6950 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_57793874370247 : Nat.Prime 57793874370247 := by
  apply lucas_primality 57793874370247 (5 : ZMod 57793874370247)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57793874370247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_96697
      · exact prime_oneHundredTenDD_279029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57793874370247) ^ 28896937185123 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 19264624790082 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 8256267767178 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 3399639668838 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 597680118 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 207124974 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_60121222230287 : Nat.Prime 60121222230287 := by
  apply lucas_primality 60121222230287 (5 : ZMod 60121222230287)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (24822965413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (24822965413, 1)] : List FactorBlock).map factorBlockValue).prod) = 60121222230287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_173
      · exact prime_oneHundredTenDD_24822965413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60121222230287) ^ 30060611115143 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 60121222230287) ^ 8588746032898 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 60121222230287) ^ 347521515782 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 60121222230287) ^ 2422 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_66139999399751 : Nat.Prime 66139999399751 := by
  apply lucas_primality 66139999399751 (7 : ZMod 66139999399751)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) = 66139999399751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_1321
      · exact prime_oneHundredTenDD_200272519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66139999399751) ^ 33069999699875 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 13227999879950 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 50068129750 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 330250 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_173
      · exact prime_oneHundredTenDD_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_179403328798297 : Nat.Prime 179403328798297 := by
  apply lucas_primality 179403328798297 (5 : ZMod 179403328798297)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (42589, 1), (2404357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (42589, 1), (2404357, 1)] : List FactorBlock).map factorBlockValue).prod) = 179403328798297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_73
      · exact prime_oneHundredTenDD_42589
      · exact prime_oneHundredTenDD_2404357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 179403328798297) ^ 89701664399148 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 59801109599432 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 2457579846552 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 4212433464 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 74615928 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_195735703302089 : Nat.Prime 195735703302089 := by
  apply lucas_primality 195735703302089 (3 : ZMod 195735703302089)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (89, 1), (11952595463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (89, 1), (11952595463, 1)] : List FactorBlock).map factorBlockValue).prod) = 195735703302089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_89
      · exact prime_oneHundredTenDD_11952595463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 195735703302089) ^ 97867851651044 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 195735703302089) ^ 8510247969656 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 195735703302089) ^ 2199277565192 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 195735703302089) ^ 16376 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_269506743853861 : Nat.Prime 269506743853861 := by
  apply lucas_primality 269506743853861 (6 : ZMod 269506743853861)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (179, 1), (229, 1), (36526547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (179, 1), (229, 1), (36526547, 1)] : List FactorBlock).map factorBlockValue).prod) = 269506743853861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_179
      · exact prime_oneHundredTenDD_229
      · exact prime_oneHundredTenDD_36526547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 269506743853861) ^ 134753371926930 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 269506743853861) ^ 89835581284620 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 269506743853861) ^ 53901348770772 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 269506743853861) ^ 1505624267340 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 269506743853861) ^ 1176885344340 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 269506743853861) ^ 7378380 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_308765963399027 : Nat.Prime 308765963399027 := by
  apply lucas_primality 308765963399027 (2 : ZMod 308765963399027)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (199, 1), (2358036103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (199, 1), (2358036103, 1)] : List FactorBlock).map factorBlockValue).prod) = 308765963399027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_47
      · exact prime_oneHundredTenDD_199
      · exact prime_oneHundredTenDD_2358036103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 308765963399027) ^ 154382981699513 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 44109423342718 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 6569488582958 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 1551587755774 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 130942 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_335707867311353 : Nat.Prime 335707867311353 := by
  apply lucas_primality 335707867311353 (3 : ZMod 335707867311353)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5879, 1), (7137860761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5879, 1), (7137860761, 1)] : List FactorBlock).map factorBlockValue).prod) = 335707867311353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5879
      · exact prime_oneHundredTenDD_7137860761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 335707867311353) ^ 167853933655676 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335707867311353) ^ 57102886088 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 335707867311353) ^ 47032 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_591592401373367 : Nat.Prime 591592401373367 := by
  apply lucas_primality 591592401373367 (5 : ZMod 591592401373367)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (7214541480163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (7214541480163, 1)] : List FactorBlock).map factorBlockValue).prod) = 591592401373367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_7214541480163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 591592401373367) ^ 295796200686683 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 591592401373367) ^ 14429082960326 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 591592401373367) ^ 82 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_643273943197409 : Nat.Prime 643273943197409 := by
  apply lucas_primality 643273943197409 (3 : ZMod 643273943197409)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1129, 1), (17805412511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1129, 1), (17805412511, 1)] : List FactorBlock).map factorBlockValue).prod) = 643273943197409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1129
      · exact prime_oneHundredTenDD_17805412511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 643273943197409) ^ 321636971598704 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 643273943197409) ^ 569773200352 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 643273943197409) ^ 36128 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_998188812141893 : Nat.Prime 998188812141893 := by
  apply lucas_primality 998188812141893 (2 : ZMod 998188812141893)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (758111, 1), (47024249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (758111, 1), (47024249, 1)] : List FactorBlock).map factorBlockValue).prod) = 998188812141893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_758111
      · exact prime_oneHundredTenDD_47024249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 998188812141893) ^ 499094406070946 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 142598401734556 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 1316678972 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 21227108 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1171415025412063 : Nat.Prime 1171415025412063 := by
  apply lucas_primality 1171415025412063 (3 : ZMod 1171415025412063)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (41, 1), (207036943339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (41, 1), (207036943339, 1)] : List FactorBlock).map factorBlockValue).prod) = 1171415025412063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_41
      · exact prime_oneHundredTenDD_207036943339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1171415025412063) ^ 585707512706031 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1171415025412063) ^ 390471675137354 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1171415025412063) ^ 50931088061394 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1171415025412063) ^ 28571098180782 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1171415025412063) ^ 5658 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_3668336598938581 : Nat.Prime 3668336598938581 := by
  apply lucas_primality 3668336598938581 (7 : ZMod 3668336598938581)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (203233, 1), (100277257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (203233, 1), (100277257, 1)] : List FactorBlock).map factorBlockValue).prod) = 3668336598938581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_203233
      · exact prime_oneHundredTenDD_100277257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3668336598938581) ^ 1834168299469290 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3668336598938581) ^ 1222778866312860 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3668336598938581) ^ 733667319787716 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3668336598938581) ^ 18049906260 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 3668336598938581) ^ 36581940 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_3860746233443951 : Nat.Prime 3860746233443951 := by
  apply lucas_primality 3860746233443951 (11 : ZMod 3860746233443951)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (4542054392287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (4542054392287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3860746233443951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_4542054392287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3860746233443951) ^ 1930373116721975 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3860746233443951) ^ 772149246688790 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3860746233443951) ^ 227102719614350 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 3860746233443951) ^ 850 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_6982819718723939 : Nat.Prime 6982819718723939 := by
  apply lucas_primality 6982819718723939 (2 : ZMod 6982819718723939)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6982819718723939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_79
      · exact prime_oneHundredTenDD_1583
      · exact prime_oneHundredTenDD_27918548017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6982819718723939) ^ 3491409859361969 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 88390123021822 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 4411130586686 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 250114 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_7028490152472379 : Nat.Prime 7028490152472379 := by
  apply lucas_primality 7028490152472379 (3 : ZMod 7028490152472379)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1171415025412063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1171415025412063, 1)] : List FactorBlock).map factorBlockValue).prod) = 7028490152472379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_1171415025412063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7028490152472379) ^ 3514245076236189 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7028490152472379) ^ 2342830050824126 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7028490152472379) ^ 6 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_7955553520153241 : Nat.Prime 7955553520153241 := by
  apply lucas_primality 7955553520153241 (3 : ZMod 7955553520153241)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (72211, 1), (144961759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (72211, 1), (144961759, 1)] : List FactorBlock).map factorBlockValue).prod) = 7955553520153241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_72211
      · exact prime_oneHundredTenDD_144961759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7955553520153241) ^ 3977776760076620 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 1591110704030648 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 418713343165960 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 110170936840 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 54880360 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8151940739207033 : Nat.Prime 8151940739207033 := by
  apply lucas_primality 8151940739207033 (3 : ZMod 8151940739207033)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8151940739207033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_997
      · exact prime_oneHundredTenDD_1022058768707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8151940739207033) ^ 4075970369603516 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 8176470149656 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 7976 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8716429397529283 : Nat.Prime 8716429397529283 := by
  apply lucas_primality 8716429397529283 (2 : ZMod 8716429397529283)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (1089503, 1), (9324443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (1089503, 1), (9324443, 1)] : List FactorBlock).map factorBlockValue).prod) = 8716429397529283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_1089503
      · exact prime_oneHundredTenDD_9324443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8716429397529283) ^ 4358214698764641 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8716429397529283) ^ 2905476465843094 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8716429397529283) ^ 792402672502662 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8716429397529283) ^ 670494569040714 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8716429397529283) ^ 8000372094 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 8716429397529283) ^ 934793574 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_18964278642836171 : Nat.Prime 18964278642836171 := by
  apply lucas_primality 18964278642836171 (6 : ZMod 18964278642836171)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (1827127, 1), (3154799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (1827127, 1), (3154799, 1)] : List FactorBlock).map factorBlockValue).prod) = 18964278642836171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_47
      · exact prime_oneHundredTenDD_1827127
      · exact prime_oneHundredTenDD_3154799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18964278642836171) ^ 9482139321418085 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 18964278642836171) ^ 3792855728567234 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 18964278642836171) ^ 2709182663262310 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 18964278642836171) ^ 403495290273110 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 18964278642836171) ^ 10379288710 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 18964278642836171) ^ 6011247830 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_22407868425741947 : Nat.Prime 22407868425741947 := by
  apply lucas_primality 22407868425741947 (2 : ZMod 22407868425741947)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (547, 1), (127220573119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (547, 1), (127220573119, 1)] : List FactorBlock).map factorBlockValue).prod) = 22407868425741947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_547
      · exact prime_oneHundredTenDD_127220573119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22407868425741947) ^ 11203934212870973 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22407868425741947) ^ 3201124060820278 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22407868425741947) ^ 974255148945302 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22407868425741947) ^ 40965024544318 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 22407868425741947) ^ 176134 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_22768684387884431 : Nat.Prime 22768684387884431 := by
  apply lucas_primality 22768684387884431 (17 : ZMod 22768684387884431)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (71887, 1), (381600983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (71887, 1), (381600983, 1)] : List FactorBlock).map factorBlockValue).prod) = 22768684387884431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_83
      · exact prime_oneHundredTenDD_71887
      · exact prime_oneHundredTenDD_381600983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 22768684387884431) ^ 11384342193942215 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 22768684387884431) ^ 4553736877576886 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 22768684387884431) ^ 274321498649210 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 22768684387884431) ^ 316728815890 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 22768684387884431) ^ 59666210 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_24193288987440403 : Nat.Prime 24193288987440403 := by
  apply lucas_primality 24193288987440403 (2 : ZMod 24193288987440403)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (263, 1), (15331615327909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (263, 1), (15331615327909, 1)] : List FactorBlock).map factorBlockValue).prod) = 24193288987440403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_263
      · exact prime_oneHundredTenDD_15331615327909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24193288987440403) ^ 12096644493720201 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24193288987440403) ^ 8064429662480134 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24193288987440403) ^ 91989691967454 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 24193288987440403) ^ 1578 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_30926241121730063 : Nat.Prime 30926241121730063 := by
  apply lucas_primality 30926241121730063 (5 : ZMod 30926241121730063)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (195735703302089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (195735703302089, 1)] : List FactorBlock).map factorBlockValue).prod) = 30926241121730063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_79
      · exact prime_oneHundredTenDD_195735703302089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 30926241121730063) ^ 15463120560865031 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 30926241121730063) ^ 391471406604178 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 30926241121730063) ^ 158 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_39013913335236331 : Nat.Prime 39013913335236331 := by
  apply lucas_primality 39013913335236331 (2 : ZMod 39013913335236331)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (10208027, 1), (127396193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (10208027, 1), (127396193, 1)] : List FactorBlock).map factorBlockValue).prod) = 39013913335236331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_10208027
      · exact prime_oneHundredTenDD_127396193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39013913335236331) ^ 19506956667618165 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39013913335236331) ^ 13004637778412110 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39013913335236331) ^ 7802782667047266 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39013913335236331) ^ 3821885790 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 39013913335236331) ^ 306240810 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_54505364198768423 : Nat.Prime 54505364198768423 := by
  apply lucas_primality 54505364198768423 (5 : ZMod 54505364198768423)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) = 54505364198768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_139
      · exact prime_oneHundredTenDD_8524454832463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54505364198768423) ^ 27252682099384211 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 2369798443424714 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 392124922293298 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 6394 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_55651003579448491 : Nat.Prime 55651003579448491 := by
  apply lucas_primality 55651003579448491 (7 : ZMod 55651003579448491)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4051, 1), (223759, 1), (2046487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4051, 1), (223759, 1), (2046487, 1)] : List FactorBlock).map factorBlockValue).prod) = 55651003579448491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_4051
      · exact prime_oneHundredTenDD_223759
      · exact prime_oneHundredTenDD_2046487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 55651003579448491) ^ 27825501789724245 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 18550334526482830 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 11130200715889698 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 13737596538990 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 248709565110 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 27193431270 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_78511797954027271 : Nat.Prime 78511797954027271 := by
  apply lucas_primality 78511797954027271 (3 : ZMod 78511797954027271)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) = 78511797954027271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_3457
      · exact prime_oneHundredTenDD_8263
      · exact prime_oneHundredTenDD_4362719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78511797954027271) ^ 39255898977013635 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 26170599318009090 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 15702359590805454 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 11215971136289610 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 22710962671110 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 9501609337290 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 17996070330 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_127305608770650061 : Nat.Prime 127305608770650061 := by
  apply lucas_primality 127305608770650061 (7 : ZMod 127305608770650061)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (5233, 1), (135152566799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (5233, 1), (135152566799, 1)] : List FactorBlock).map factorBlockValue).prod) = 127305608770650061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_5233
      · exact prime_oneHundredTenDD_135152566799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 127305608770650061) ^ 63652804385325030 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 127305608770650061) ^ 42435202923550020 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 127305608770650061) ^ 25461121754130012 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 127305608770650061) ^ 24327462023820 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 127305608770650061) ^ 941940 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_133962282976311967 : Nat.Prime 133962282976311967 := by
  apply lucas_primality 133962282976311967 (3 : ZMod 133962282976311967)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (463, 1), (4383869460577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (463, 1), (4383869460577, 1)] : List FactorBlock).map factorBlockValue).prod) = 133962282976311967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_463
      · exact prime_oneHundredTenDD_4383869460577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133962282976311967) ^ 66981141488155983 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 44654094325437322 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 12178389361482906 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 289335384398082 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 30558 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_136496538697859633 : Nat.Prime 136496538697859633 := by
  apply lucas_primality 136496538697859633 (3 : ZMod 136496538697859633)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (488417, 1), (919300049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (488417, 1), (919300049, 1)] : List FactorBlock).map factorBlockValue).prod) = 136496538697859633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_488417
      · exact prime_oneHundredTenDD_919300049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 136496538697859633) ^ 68248269348929816 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 136496538697859633) ^ 7184028352518928 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 136496538697859633) ^ 279467214896 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 136496538697859633) ^ 148478768 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_143321738727393937 : Nat.Prime 143321738727393937 := by
  apply lucas_primality 143321738727393937 (5 : ZMod 143321738727393937)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (52383676435451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (52383676435451, 1)] : List FactorBlock).map factorBlockValue).prod) = 143321738727393937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_52383676435451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 143321738727393937) ^ 71660869363696968 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 143321738727393937) ^ 47773912909131312 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 143321738727393937) ^ 7543249406704944 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 143321738727393937) ^ 2736 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_148228709119623551 : Nat.Prime 148228709119623551 := by
  apply lucas_primality 148228709119623551 (11 : ZMod 148228709119623551)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (269506743853861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (269506743853861, 1)] : List FactorBlock).map factorBlockValue).prod) = 148228709119623551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_269506743853861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 148228709119623551) ^ 74114354559811775 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 148228709119623551) ^ 29645741823924710 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 148228709119623551) ^ 13475337192693050 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 148228709119623551) ^ 550 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_170021964029785961 : Nat.Prime 170021964029785961 := by
  apply lucas_primality 170021964029785961 (3 : ZMod 170021964029785961)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (14078959, 1), (301907911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (14078959, 1), (301907911, 1)] : List FactorBlock).map factorBlockValue).prod) = 170021964029785961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_14078959
      · exact prime_oneHundredTenDD_301907911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 170021964029785961) ^ 85010982014892980 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 170021964029785961) ^ 34004392805957192 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 170021964029785961) ^ 12076316440 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 170021964029785961) ^ 563158360 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_257138647306974463 : Nat.Prime 257138647306974463 := by
  apply lucas_primality 257138647306974463 (5 : ZMod 257138647306974463)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229841, 1), (186461254597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229841, 1), (186461254597, 1)] : List FactorBlock).map factorBlockValue).prod) = 257138647306974463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_229841
      · exact prime_oneHundredTenDD_186461254597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 257138647306974463) ^ 128569323653487231 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 85712882435658154 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 1118767527582 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 1379046 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_343761494570627743 : Nat.Prime 343761494570627743 := by
  apply lucas_primality 343761494570627743 (3 : ZMod 343761494570627743)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (71, 1), (73, 1), (3209, 1), (18226079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (71, 1), (73, 1), (3209, 1), (18226079, 1)] : List FactorBlock).map factorBlockValue).prod) = 343761494570627743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_73
      · exact prime_oneHundredTenDD_3209
      · exact prime_oneHundredTenDD_18226079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 343761494570627743) ^ 171880747285313871 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 343761494570627743) ^ 114587164856875914 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 343761494570627743) ^ 49108784938661106 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 343761494570627743) ^ 4841711191135602 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 343761494570627743) ^ 4709061569460654 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 343761494570627743) ^ 107124180296238 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 343761494570627743) ^ 18860968098 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_911676659536508311 : Nat.Prime 911676659536508311 := by
  apply lucas_primality 911676659536508311 (6 : ZMod 911676659536508311)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (15173, 1), (667616203883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (15173, 1), (667616203883, 1)] : List FactorBlock).map factorBlockValue).prod) = 911676659536508311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_15173
      · exact prime_oneHundredTenDD_667616203883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 911676659536508311) ^ 455838329768254155 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 303892219845502770 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 182335331907301662 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 60085458349470 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 1365570 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_958095564164668681 : Nat.Prime 958095564164668681 := by
  apply lucas_primality 958095564164668681 (13 : ZMod 958095564164668681)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (12601, 1), (791773, 1), (800243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (12601, 1), (791773, 1), (800243, 1)] : List FactorBlock).map factorBlockValue).prod) = 958095564164668681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_12601
      · exact prime_oneHundredTenDD_791773
      · exact prime_oneHundredTenDD_800243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 958095564164668681) ^ 479047782082334340 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 319365188054889560 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 191619112832933736 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 76033296100680 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 1210063445160 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 1197255788760 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1109188763774599357 : Nat.Prime 1109188763774599357 := by
  apply lucas_primality 1109188763774599357 (5 : ZMod 1109188763774599357)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109188763774599357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_89
      · exact prime_oneHundredTenDD_199
      · exact prime_oneHundredTenDD_29485457179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1109188763774599357) ^ 554594381887299678 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 369729587924866452 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 18799809555501684 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 12462795098591004 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 5573812883289444 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 37618164 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2043146173337516953 : Nat.Prime 2043146173337516953 := by
  apply lucas_primality 2043146173337516953 (5 : ZMod 2043146173337516953)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (107, 1), (2797, 1), (11083, 1), (450277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (107, 1), (2797, 1), (11083, 1), (450277, 1)] : List FactorBlock).map factorBlockValue).prod) = 2043146173337516953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_107
      · exact prime_oneHundredTenDD_2797
      · exact prime_oneHundredTenDD_11083
      · exact prime_oneHundredTenDD_450277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2043146173337516953) ^ 1021573086668758476 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2043146173337516953) ^ 681048724445838984 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2043146173337516953) ^ 107534009123027208 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2043146173337516953) ^ 19094824049883336 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2043146173337516953) ^ 730477716602616 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2043146173337516953) ^ 184349559987144 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 2043146173337516953) ^ 4537531726776 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_101
      · exact prime_oneHundredTenDD_191
      · exact prime_oneHundredTenDD_48017
      · exact prime_oneHundredTenDD_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_3553185310071156919 : Nat.Prime 3553185310071156919 := by
  apply lucas_primality 3553185310071156919 (3 : ZMod 3553185310071156919)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (45149417, 1), (59892211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (45149417, 1), (59892211, 1)] : List FactorBlock).map factorBlockValue).prod) = 3553185310071156919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_73
      · exact prime_oneHundredTenDD_45149417
      · exact prime_oneHundredTenDD_59892211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3553185310071156919) ^ 1776592655035578459 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3553185310071156919) ^ 1184395103357052306 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3553185310071156919) ^ 48673771370837766 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3553185310071156919) ^ 78698365254 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3553185310071156919) ^ 59326333938 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_4969233525257565349 : Nat.Prime 4969233525257565349 := by
  apply lucas_primality 4969233525257565349 (2 : ZMod 4969233525257565349)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (13020991, 1), (228796471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (13020991, 1), (228796471, 1)] : List FactorBlock).map factorBlockValue).prod) = 4969233525257565349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_139
      · exact prime_oneHundredTenDD_13020991
      · exact prime_oneHundredTenDD_228796471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4969233525257565349) ^ 2484616762628782674 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4969233525257565349) ^ 1656411175085855116 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4969233525257565349) ^ 35749881476673132 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4969233525257565349) ^ 381632513628 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 4969233525257565349) ^ 21719012988 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_5011406982273367241 : Nat.Prime 5011406982273367241 := by
  apply lucas_primality 5011406982273367241 (3 : ZMod 5011406982273367241)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (113, 1), (8559401, 1), (129532237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (113, 1), (8559401, 1), (129532237, 1)] : List FactorBlock).map factorBlockValue).prod) = 5011406982273367241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_113
      · exact prime_oneHundredTenDD_8559401
      · exact prime_oneHundredTenDD_129532237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5011406982273367241) ^ 2505703491136683620 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5011406982273367241) ^ 1002281396454673448 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5011406982273367241) ^ 44348734356401480 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5011406982273367241) ^ 585485711240 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5011406982273367241) ^ 38688492520 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_12397982967159602339 : Nat.Prime 12397982967159602339 := by
  apply lucas_primality 12397982967159602339 (2 : ZMod 12397982967159602339)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (12690113, 1), (21238689431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (12690113, 1), (21238689431, 1)] : List FactorBlock).map factorBlockValue).prod) = 12397982967159602339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_12690113
      · exact prime_oneHundredTenDD_21238689431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12397982967159602339) ^ 6198991483579801169 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12397982967159602339) ^ 539042737702591406 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12397982967159602339) ^ 976979713826 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 12397982967159602339) ^ 583745198 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_35653477162396384699 : Nat.Prime 35653477162396384699 := by
  apply lucas_primality 35653477162396384699 (3 : ZMod 35653477162396384699)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (229, 1), (1523, 1), (847991, 1), (1826549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (229, 1), (1523, 1), (847991, 1), (1826549, 1)] : List FactorBlock).map factorBlockValue).prod) = 35653477162396384699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_229
      · exact prime_oneHundredTenDD_1523
      · exact prime_oneHundredTenDD_847991
      · exact prime_oneHundredTenDD_1826549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35653477162396384699) ^ 17826738581198192349 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 11884492387465461566 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 3241225196581489518 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 155692040010464562 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 23410030966773726 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 42044640995478 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 19519584288402 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_38191682631195018301 : Nat.Prime 38191682631195018301 := by
  apply lucas_primality 38191682631195018301 (2 : ZMod 38191682631195018301)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (127305608770650061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (127305608770650061, 1)] : List FactorBlock).map factorBlockValue).prod) = 38191682631195018301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_127305608770650061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38191682631195018301) ^ 19095841315597509150 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38191682631195018301) ^ 12730560877065006100 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38191682631195018301) ^ 7638336526239003660 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 38191682631195018301) ^ 300 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_2063
      · exact prime_oneHundredTenDD_15269
      · exact prime_oneHundredTenDD_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_124664600840500529999 : Nat.Prime 124664600840500529999 := by
  apply lucas_primality 124664600840500529999 (7 : ZMod 124664600840500529999)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (4003, 1), (60121222230287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (4003, 1), (60121222230287, 1)] : List FactorBlock).map factorBlockValue).prod) = 124664600840500529999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_37
      · exact prime_oneHundredTenDD_4003
      · exact prime_oneHundredTenDD_60121222230287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 124664600840500529999) ^ 62332300420250264999 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 124664600840500529999) ^ 17809228691500075714 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 124664600840500529999) ^ 3369313536229744054 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 124664600840500529999) ^ 31142793115288666 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 124664600840500529999) ^ 2073554 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_224952136074415902667 : Nat.Prime 224952136074415902667 := by
  apply lucas_primality 224952136074415902667 (3 : ZMod 224952136074415902667)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (19853, 1), (100271, 1), (355354249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (19853, 1), (100271, 1), (355354249, 1)] : List FactorBlock).map factorBlockValue).prod) = 224952136074415902667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_53
      · exact prime_oneHundredTenDD_19853
      · exact prime_oneHundredTenDD_100271
      · exact prime_oneHundredTenDD_355354249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 224952136074415902667) ^ 112476068037207951333 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 74984045358138634222 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 4244379925932375522 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 11330888836670322 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 2243441633916246 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 633036291834 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_246852669850875834709 : Nat.Prime 246852669850875834709 := by
  apply lucas_primality 246852669850875834709 (6 : ZMod 246852669850875834709)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (139, 1), (7867, 1), (990099933397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (139, 1), (7867, 1), (990099933397, 1)] : List FactorBlock).map factorBlockValue).prod) = 246852669850875834709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_139
      · exact prime_oneHundredTenDD_7867
      · exact prime_oneHundredTenDD_990099933397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 246852669850875834709) ^ 123426334925437917354 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 246852669850875834709) ^ 82284223283625278236 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 246852669850875834709) ^ 12992245781625043932 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 246852669850875834709) ^ 1775918488135797372 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 246852669850875834709) ^ 31378247089217724 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 246852669850875834709) ^ 249320964 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_277042283689663805783 : Nat.Prime 277042283689663805783 := by
  apply lucas_primality 277042283689663805783 (5 : ZMod 277042283689663805783)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2327173, 1), (8503336257881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2327173, 1), (8503336257881, 1)] : List FactorBlock).map factorBlockValue).prod) = 277042283689663805783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_2327173
      · exact prime_oneHundredTenDD_8503336257881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277042283689663805783) ^ 138521141844831902891 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 277042283689663805783) ^ 39577469098523400826 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 277042283689663805783) ^ 119046707610334 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 277042283689663805783) ^ 32580422 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_289837372619434363439 : Nat.Prime 289837372619434363439 := by
  apply lucas_primality 289837372619434363439 (7 : ZMod 289837372619434363439)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (13, 1), (12511, 1), (282001, 1), (26112773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (13, 1), (12511, 1), (282001, 1), (26112773, 1)] : List FactorBlock).map factorBlockValue).prod) = 289837372619434363439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_12511
      · exact prime_oneHundredTenDD_282001
      · exact prime_oneHundredTenDD_26112773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 289837372619434363439) ^ 144918686309717181719 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 289837372619434363439) ^ 26348852056312214858 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 289837372619434363439) ^ 22295182509187258726 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 289837372619434363439) ^ 23166603198739858 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 289837372619434363439) ^ 1027788456847438 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 289837372619434363439) ^ 11099448251606 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_308982765336835019951 : Nat.Prime 308982765336835019951 := by
  apply lucas_primality 308982765336835019951 (11 : ZMod 308982765336835019951)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (29, 1), (7129, 1), (21751, 1), (105709753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (29, 1), (7129, 1), (21751, 1), (105709753, 1)] : List FactorBlock).map factorBlockValue).prod) = 308982765336835019951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_29
      · exact prime_oneHundredTenDD_7129
      · exact prime_oneHundredTenDD_21751
      · exact prime_oneHundredTenDD_105709753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 308982765336835019951) ^ 154491382668417509975 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 308982765336835019951) ^ 61796553067367003990 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 308982765336835019951) ^ 23767905025910386150 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 308982765336835019951) ^ 10654578115063276550 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 308982765336835019951) ^ 43341669986931550 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 308982765336835019951) ^ 14205451029232450 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 308982765336835019951) ^ 2922935269150 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_371883461788350702353 : Nat.Prime 371883461788350702353 := by
  apply lucas_primality 371883461788350702353 (3 : ZMod 371883461788350702353)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (101, 1), (1682531, 1), (136773649087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (101, 1), (1682531, 1), (136773649087, 1)] : List FactorBlock).map factorBlockValue).prod) = 371883461788350702353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_101
      · exact prime_oneHundredTenDD_1682531
      · exact prime_oneHundredTenDD_136773649087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 371883461788350702353) ^ 185941730894175351176 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 371883461788350702353) ^ 3682014473151987152 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 371883461788350702353) ^ 221026216924592 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 371883461788350702353) ^ 2718970096 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_516843125390944643623 : Nat.Prime 516843125390944643623 := by
  apply lucas_primality 516843125390944643623 (3 : ZMod 516843125390944643623)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1076762003, 1), (4210504841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1076762003, 1), (4210504841, 1)] : List FactorBlock).map factorBlockValue).prod) = 516843125390944643623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_19
      · exact prime_oneHundredTenDD_1076762003
      · exact prime_oneHundredTenDD_4210504841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 516843125390944643623) ^ 258421562695472321811 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 172281041796981547874 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 27202269757418139138 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 479997551874 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 122750868342 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_733814796752556207677 : Nat.Prime 733814796752556207677 := by
  apply lucas_primality 733814796752556207677 (2 : ZMod 733814796752556207677)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (83, 1), (170021964029785961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (83, 1), (170021964029785961, 1)] : List FactorBlock).map factorBlockValue).prod) = 733814796752556207677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_83
      · exact prime_oneHundredTenDD_170021964029785961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 733814796752556207677) ^ 366907398376278103838 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 733814796752556207677) ^ 56447292057888939052 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 733814796752556207677) ^ 8841142129548869972 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 733814796752556207677) ^ 4316 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_743766923576701404707 : Nat.Prime 743766923576701404707 := by
  apply lucas_primality 743766923576701404707 (2 : ZMod 743766923576701404707)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (371883461788350702353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (371883461788350702353, 1)] : List FactorBlock).map factorBlockValue).prod) = 743766923576701404707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_371883461788350702353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 743766923576701404707) ^ 371883461788350702353 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 743766923576701404707) ^ 2 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_199
      · exact prime_oneHundredTenDD_52864081
      · exact prime_oneHundredTenDD_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1550411355806685423811 : Nat.Prime 1550411355806685423811 := by
  apply lucas_primality 1550411355806685423811 (2 : ZMod 1550411355806685423811)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1550411355806685423811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_3283807
      · exact prime_oneHundredTenDD_476907466417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1550411355806685423811) ^ 775205677903342711905 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 516803785268895141270 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 310082271161337084762 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 140946486891516856710 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 472138391752830 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 3250968930 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_5000910483656400298243 : Nat.Prime 5000910483656400298243 := by
  apply lucas_primality 5000910483656400298243 (2 : ZMod 5000910483656400298243)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (881, 1), (55651003579448491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (881, 1), (55651003579448491, 1)] : List FactorBlock).map factorBlockValue).prod) = 5000910483656400298243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_881
      · exact prime_oneHundredTenDD_55651003579448491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5000910483656400298243) ^ 2500455241828200149121 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 1666970161218800099414 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 294171204920964723426 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 5676402365103746082 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 89862 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_5217072707149818541903 : Nat.Prime 5217072707149818541903 := by
  apply lucas_primality 5217072707149818541903 (3 : ZMod 5217072707149818541903)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (289837372619434363439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (289837372619434363439, 1)] : List FactorBlock).map factorBlockValue).prod) = 5217072707149818541903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_289837372619434363439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5217072707149818541903) ^ 2608536353574909270951 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5217072707149818541903) ^ 1739024235716606180634 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 5217072707149818541903) ^ 18 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8695344076653562208641 : Nat.Prime 8695344076653562208641 := by
  apply lucas_primality 8695344076653562208641 (7 : ZMod 8695344076653562208641)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 1), (11527, 1), (2668993, 1), (16356083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 1), (11527, 1), (2668993, 1), (16356083, 1)] : List FactorBlock).map factorBlockValue).prod) = 8695344076653562208641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_11527
      · exact prime_oneHundredTenDD_2668993
      · exact prime_oneHundredTenDD_16356083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8695344076653562208641) ^ 4347672038326781104320 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 2898448025551187402880 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 1739068815330712441728 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 754345803474760320 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 3257911907844480 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 531627534334080 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_8968807997203239919541 : Nat.Prime 8968807997203239919541 := by
  apply lucas_primality 8968807997203239919541 (3 : ZMod 8968807997203239919541)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (2027, 1), (3353087, 1), (1118289247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (2027, 1), (3353087, 1), (1118289247, 1)] : List FactorBlock).map factorBlockValue).prod) = 8968807997203239919541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_2027
      · exact prime_oneHundredTenDD_3353087
      · exact prime_oneHundredTenDD_1118289247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8968807997203239919541) ^ 4484403998601619959770 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8968807997203239919541) ^ 1793761599440647983908 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8968807997203239919541) ^ 152013694867851524060 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8968807997203239919541) ^ 4424670940899477020 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8968807997203239919541) ^ 2674791318329420 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 8968807997203239919541) ^ 8020114671820 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_15200129274940369969381 : Nat.Prime 15200129274940369969381 := by
  apply lucas_primality 15200129274940369969381 (6 : ZMod 15200129274940369969381)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (947, 1), (42571, 1), (479861, 1), (4365113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (947, 1), (42571, 1), (479861, 1), (4365113, 1)] : List FactorBlock).map factorBlockValue).prod) = 15200129274940369969381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_947
      · exact prime_oneHundredTenDD_42571
      · exact prime_oneHundredTenDD_479861
      · exact prime_oneHundredTenDD_4365113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15200129274940369969381) ^ 7600064637470184984690 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 15200129274940369969381) ^ 5066709758313456656460 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 15200129274940369969381) ^ 3040025854988073993876 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 15200129274940369969381) ^ 16050822888004614540 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 15200129274940369969381) ^ 357053611024884780 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 15200129274940369969381) ^ 31676108862650580 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (6 : ZMod 15200129274940369969381) ^ 3482184602080260 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_16626633921813454641187 : Nat.Prime 16626633921813454641187 := by
  apply lucas_primality 16626633921813454641187 (2 : ZMod 16626633921813454641187)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (103, 1), (907, 1), (485567, 1), (8726927519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (103, 1), (907, 1), (485567, 1), (8726927519, 1)] : List FactorBlock).map factorBlockValue).prod) = 16626633921813454641187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_103
      · exact prime_oneHundredTenDD_907
      · exact prime_oneHundredTenDD_485567
      · exact prime_oneHundredTenDD_8726927519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16626633921813454641187) ^ 8313316960906727320593 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16626633921813454641187) ^ 5542211307271151547062 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16626633921813454641187) ^ 2375233417401922091598 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16626633921813454641187) ^ 161423630308868491662 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16626633921813454641187) ^ 18331459671238648998 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16626633921813454641187) ^ 34241688421604958 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 16626633921813454641187) ^ 1905210497694 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_27039711302886072957109 : Nat.Prime 27039711302886072957109 := by
  apply lucas_primality 27039711302886072957109 (7 : ZMod 27039711302886072957109)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (38191682631195018301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (38191682631195018301, 1)] : List FactorBlock).map factorBlockValue).prod) = 27039711302886072957109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_59
      · exact prime_oneHundredTenDD_38191682631195018301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 27039711302886072957109) ^ 13519855651443036478554 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 27039711302886072957109) ^ 9013237100962024319036 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 27039711302886072957109) ^ 458300191574340219612 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 27039711302886072957109) ^ 708 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_35853529750253765128927 : Nat.Prime 35853529750253765128927 := by
  apply lucas_primality 35853529750253765128927 (3 : ZMod 35853529750253765128927)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853529750253765128927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_8317
      · exact prime_oneHundredTenDD_66139999399751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853529750253765128927) ^ 17926764875126882564463 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 11951176583417921709642 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 2109031161779633242878 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 504979292257095283506 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 4310872880876970678 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 542085426 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_45500073735083115287453 : Nat.Prime 45500073735083115287453 := by
  apply lucas_primality 45500073735083115287453 (2 : ZMod 45500073735083115287453)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1393023833, 1), (8165702670911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1393023833, 1), (8165702670911, 1)] : List FactorBlock).map factorBlockValue).prod) = 45500073735083115287453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1393023833
      · exact prime_oneHundredTenDD_8165702670911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45500073735083115287453) ^ 22750036867541557643726 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45500073735083115287453) ^ 32662810683644 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 45500073735083115287453) ^ 5572095332 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_156718638043002296895919 : Nat.Prime 156718638043002296895919 := by
  apply lucas_primality 156718638043002296895919 (3 : ZMod 156718638043002296895919)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21557, 1), (78347, 1), (393013, 1), (39350639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21557, 1), (78347, 1), (393013, 1), (39350639, 1)] : List FactorBlock).map factorBlockValue).prod) = 156718638043002296895919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_21557
      · exact prime_oneHundredTenDD_78347
      · exact prime_oneHundredTenDD_393013
      · exact prime_oneHundredTenDD_39350639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 156718638043002296895919) ^ 78359319021501148447959 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 156718638043002296895919) ^ 52239546014334098965306 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 156718638043002296895919) ^ 7269965117734485174 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 156718638043002296895919) ^ 2000314473342977994 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 156718638043002296895919) ^ 398761969815253686 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 156718638043002296895919) ^ 3982619902131762 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_215121178501522590773563 : Nat.Prime 215121178501522590773563 := by
  apply lucas_primality 215121178501522590773563 (2 : ZMod 215121178501522590773563)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) = 215121178501522590773563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_35853529750253765128927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215121178501522590773563) ^ 107560589250761295386781 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 71707059500507530257854 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 6 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_477191061755581812807533 : Nat.Prime 477191061755581812807533 := by
  apply lucas_primality 477191061755581812807533 (3 : ZMod 477191061755581812807533)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (43, 1), (8311, 1), (3668336598938581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (43, 1), (8311, 1), (3668336598938581, 1)] : List FactorBlock).map factorBlockValue).prod) = 477191061755581812807533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_43
      · exact prime_oneHundredTenDD_8311
      · exact prime_oneHundredTenDD_3668336598938581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 477191061755581812807533) ^ 238595530877790906403766 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 477191061755581812807533) ^ 68170151679368830401076 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 477191061755581812807533) ^ 36707004750429370215964 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 477191061755581812807533) ^ 11097466552455390995524 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 477191061755581812807533) ^ 57416804446586669812 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 477191061755581812807533) ^ 130083772 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_724395956348371658049161 : Nat.Prime 724395956348371658049161 := by
  apply lucas_primality 724395956348371658049161 (3 : ZMod 724395956348371658049161)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (59723, 1), (536563, 1), (7339440673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (59723, 1), (536563, 1), (7339440673, 1)] : List FactorBlock).map factorBlockValue).prod) = 724395956348371658049161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_59723
      · exact prime_oneHundredTenDD_536563
      · exact prime_oneHundredTenDD_7339440673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 724395956348371658049161) ^ 362197978174185829024580 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 144879191269674331609832 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 103485136621195951149880 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 65854177849851968913560 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 12129262701946848920 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 1350066919165823320 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 98699068310920 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_937941619075616044443361 : Nat.Prime 937941619075616044443361 := by
  apply lucas_primality 937941619075616044443361 (7 : ZMod 937941619075616044443361)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (23, 2), (3257, 1), (4051, 1), (279961876619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (23, 2), (3257, 1), (4051, 1), (279961876619, 1)] : List FactorBlock).map factorBlockValue).prod) = 937941619075616044443361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_23
      · exact prime_oneHundredTenDD_3257
      · exact prime_oneHundredTenDD_4051
      · exact prime_oneHundredTenDD_279961876619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 937941619075616044443361) ^ 468970809537808022221680 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 937941619075616044443361) ^ 312647206358538681481120 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 937941619075616044443361) ^ 187588323815123208888672 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 937941619075616044443361) ^ 40780070394592001932320 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 937941619075616044443361) ^ 287977162749651840480 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 937941619075616044443361) ^ 231533354499041235360 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 937941619075616044443361) ^ 3350247649440 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_3940411987980561962981753 : Nat.Prime 3940411987980561962981753 := by
  apply lucas_primality 3940411987980561962981753 (3 : ZMod 3940411987980561962981753)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (953, 1), (516843125390944643623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (953, 1), (516843125390944643623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3940411987980561962981753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_953
      · exact prime_oneHundredTenDD_516843125390944643623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3940411987980561962981753) ^ 1970205993990280981490876 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3940411987980561962981753) ^ 4134745003127557148984 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 3940411987980561962981753) ^ 7624 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_6861676634375057617593509 : Nat.Prime 6861676634375057617593509 := by
  apply lucas_primality 6861676634375057617593509 (2 : ZMod 6861676634375057617593509)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) = 6861676634375057617593509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_210430769
      · exact prime_oneHundredTenDD_8151940739207033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6861676634375057617593509) ^ 3430838317187528808796754 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 32607762956828132 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 841723076 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_14849207267790644784910913 : Nat.Prime 14849207267790644784910913 := by
  apply lucas_primality 14849207267790644784910913 (3 : ZMod 14849207267790644784910913)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (131, 1), (349, 1), (461, 1), (93947437, 1), (117176551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (131, 1), (349, 1), (461, 1), (93947437, 1), (117176551, 1)] : List FactorBlock).map factorBlockValue).prod) = 14849207267790644784910913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_131
      · exact prime_oneHundredTenDD_349
      · exact prime_oneHundredTenDD_461
      · exact prime_oneHundredTenDD_93947437
      · exact prime_oneHundredTenDD_117176551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14849207267790644784910913) ^ 7424603633895322392455456 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 113352727235043089961152 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 42547871827480357549888 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 32210861752257363958592 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 158058673466426176 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 126725075461477312 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_41430187082290687169878871 : Nat.Prime 41430187082290687169878871 := by
  apply lucas_primality 41430187082290687169878871 (17 : ZMod 41430187082290687169878871)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (2399, 1), (211275487, 1), (628773431723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (2399, 1), (211275487, 1), (628773431723, 1)] : List FactorBlock).map factorBlockValue).prod) = 41430187082290687169878871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_13
      · exact prime_oneHundredTenDD_2399
      · exact prime_oneHundredTenDD_211275487
      · exact prime_oneHundredTenDD_628773431723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 41430187082290687169878871) ^ 20715093541145343584939435 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 41430187082290687169878871) ^ 8286037416458137433975774 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 41430187082290687169878871) ^ 3186937467868514397682990 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 41430187082290687169878871) ^ 17269773689991949633130 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 41430187082290687169878871) ^ 196095570151452010 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (17 : ZMod 41430187082290687169878871) ^ 65890486130690 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_344045918654260494778438561 : Nat.Prime 344045918654260494778438561 := by
  apply lucas_primality 344045918654260494778438561 (7 : ZMod 344045918654260494778438561)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (89, 1), (131, 1), (1031, 1), (11352647, 1), (1750801123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (89, 1), (131, 1), (1031, 1), (11352647, 1), (1750801123, 1)] : List FactorBlock).map factorBlockValue).prod) = 344045918654260494778438561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_89
      · exact prime_oneHundredTenDD_131
      · exact prime_oneHundredTenDD_1031
      · exact prime_oneHundredTenDD_11352647
      · exact prime_oneHundredTenDD_1750801123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 344045918654260494778438561) ^ 172022959327130247389219280 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 114681972884753498259479520 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 68809183730852098955687712 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 3865684479261353873915040 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 2626304722551606830369760 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 333701182011891847505760 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 30305348052684144480 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 196507709604810720 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_909436064694478790393355077 : Nat.Prime 909436064694478790393355077 := by
  apply lucas_primality 909436064694478790393355077 (2 : ZMod 909436064694478790393355077)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478790393355077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_4171314503
      · exact prime_oneHundredTenDD_54505364198768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 909436064694478790393355077) ^ 454718032347239395196677538 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 218021456795073692 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 16685258012 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1130863976098351887184780661 : Nat.Prime 1130863976098351887184780661 := by
  apply lucas_primality 1130863976098351887184780661 (2 : ZMod 1130863976098351887184780661)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (56645794981, 1), (998188812141893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (56645794981, 1), (998188812141893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130863976098351887184780661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_56645794981
      · exact prime_oneHundredTenDD_998188812141893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130863976098351887184780661) ^ 565431988049175943592390330 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 226172795219670377436956132 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 19963776242837860 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 1132915899620 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1398380185497962011034943829 : Nat.Prime 1398380185497962011034943829 := by
  apply lucas_primality 1398380185497962011034943829 (2 : ZMod 1398380185497962011034943829)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (61, 1), (3251, 1), (371387, 1), (5760091, 1), (30520993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (61, 1), (3251, 1), (371387, 1), (5760091, 1), (30520993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1398380185497962011034943829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_61
      · exact prime_oneHundredTenDD_3251
      · exact prime_oneHundredTenDD_371387
      · exact prime_oneHundredTenDD_5760091
      · exact prime_oneHundredTenDD_30520993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1398380185497962011034943829) ^ 699190092748981005517471914 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398380185497962011034943829) ^ 466126728499320670344981276 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398380185497962011034943829) ^ 22924265336032164115326948 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398380185497962011034943829) ^ 430138476006755463252828 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398380185497962011034943829) ^ 3765291153158193504444 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398380185497962011034943829) ^ 242770502323307394108 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 1398380185497962011034943829) ^ 45816995059694224596 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_1625616965641380837828122201 : Nat.Prime 1625616965641380837828122201 := by
  apply lucas_primality 1625616965641380837828122201 (3 : ZMod 1625616965641380837828122201)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1625616965641380837828122201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_171401
      · exact prime_oneHundredTenDD_714027719
      · exact prime_oneHundredTenDD_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1625616965641380837828122201) ^ 812808482820690418914061100 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 325123393128276167565624440 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 9484291023047595042200 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 2276686075882413800 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 269247143141501800 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2322309950916258339754460287 : Nat.Prime 2322309950916258339754460287 := by
  apply lucas_primality 2322309950916258339754460287 (3 : ZMod 2322309950916258339754460287)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (709, 1), (95656009, 1), (335707867311353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (709, 1), (95656009, 1), (335707867311353, 1)] : List FactorBlock).map factorBlockValue).prod) = 2322309950916258339754460287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_709
      · exact prime_oneHundredTenDD_95656009
      · exact prime_oneHundredTenDD_335707867311353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2322309950916258339754460287) ^ 1161154975458129169877230143 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322309950916258339754460287) ^ 774103316972086113251486762 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322309950916258339754460287) ^ 136606467700956372926732958 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322309950916258339754460287) ^ 3275472427244370013758054 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322309950916258339754460287) ^ 24277721548222426254 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 2322309950916258339754460287) ^ 6917651258862 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_2767007601091712064388293107 : Nat.Prime 2767007601091712064388293107 := by
  apply lucas_primality 2767007601091712064388293107 (2 : ZMod 2767007601091712064388293107)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (71, 1), (2819, 1), (39619, 1), (44549, 1), (230375632811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (71, 1), (2819, 1), (39619, 1), (44549, 1), (230375632811, 1)] : List FactorBlock).map factorBlockValue).prod) = 2767007601091712064388293107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_17
      · exact prime_oneHundredTenDD_71
      · exact prime_oneHundredTenDD_2819
      · exact prime_oneHundredTenDD_39619
      · exact prime_oneHundredTenDD_44549
      · exact prime_oneHundredTenDD_230375632811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2767007601091712064388293107) ^ 1383503800545856032194146553 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2767007601091712064388293107) ^ 162765153005394827316958418 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2767007601091712064388293107) ^ 38971938043545240343497086 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2767007601091712064388293107) ^ 981556438840621519825574 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2767007601091712064388293107) ^ 69840420028060073812774 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2767007601091712064388293107) ^ 62111553594731914619594 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 2767007601091712064388293107) ^ 12010851874085846 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_4484460594872774725043095727 : Nat.Prime 4484460594872774725043095727 := by
  apply lucas_primality 4484460594872774725043095727 (5 : ZMod 4484460594872774725043095727)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (14849207267790644784910913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (14849207267790644784910913, 1)] : List FactorBlock).map factorBlockValue).prod) = 4484460594872774725043095727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_151
      · exact prime_oneHundredTenDD_14849207267790644784910913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4484460594872774725043095727) ^ 2242230297436387362521547863 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4484460594872774725043095727) ^ 29698414535581289569821826 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 4484460594872774725043095727) ^ 302 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_6502467862565523351312488803 : Nat.Prime 6502467862565523351312488803 := by
  apply lucas_primality 6502467862565523351312488803 (2 : ZMod 6502467862565523351312488803)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 6502467862565523351312488803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_107
      · exact prime_oneHundredTenDD_43001837
      · exact prime_oneHundredTenDD_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6502467862565523351312488803) ^ 3251233931282761675656244401 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 2167489287521841117104162934 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 60770727687528255619742886 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 151213722859456523946 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 82821538062 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_10003796711639266694326905853 : Nat.Prime 10003796711639266694326905853 := by
  apply lucas_primality 10003796711639266694326905853 (2 : ZMod 10003796711639266694326905853)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (2893777, 1), (2043146173337516953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (2893777, 1), (2043146173337516953, 1)] : List FactorBlock).map factorBlockValue).prod) = 10003796711639266694326905853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_47
      · exact prime_oneHundredTenDD_2893777
      · exact prime_oneHundredTenDD_2043146173337516953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10003796711639266694326905853) ^ 5001898355819633347163452926 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10003796711639266694326905853) ^ 3334598903879755564775635284 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10003796711639266694326905853) ^ 212846738545516312645253316 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10003796711639266694326905853) ^ 3457003325287078684476 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 10003796711639266694326905853) ^ 4896270684 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_26009871450262093405249955219 : Nat.Prime 26009871450262093405249955219 := by
  apply lucas_primality 26009871450262093405249955219 (2 : ZMod 26009871450262093405249955219)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1579, 1), (70729, 1), (377137, 1), (308765963399027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1579, 1), (70729, 1), (377137, 1), (308765963399027, 1)] : List FactorBlock).map factorBlockValue).prod) = 26009871450262093405249955219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_1579
      · exact prime_oneHundredTenDD_70729
      · exact prime_oneHundredTenDD_377137
      · exact prime_oneHundredTenDD_308765963399027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26009871450262093405249955219) ^ 13004935725131046702624977609 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26009871450262093405249955219) ^ 16472369506182453074889142 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26009871450262093405249955219) ^ 367739844339126714717442 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26009871450262093405249955219) ^ 68966639312138807396914 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 26009871450262093405249955219) ^ 84238143232934 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_32512339312827616756562444023 : Nat.Prime 32512339312827616756562444023 := by
  apply lucas_primality 32512339312827616756562444023 (3 : ZMod 32512339312827616756562444023)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) = 32512339312827616756562444023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_11
      · exact prime_oneHundredTenDD_5879
      · exact prime_oneHundredTenDD_35267
      · exact prime_oneHundredTenDD_88812211
      · exact prime_oneHundredTenDD_26752207429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32512339312827616756562444023) ^ 16256169656413808378281222011 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32512339312827616756562444023) ^ 10837446437609205585520814674 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32512339312827616756562444023) ^ 2955667210257056068778404002 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32512339312827616756562444023) ^ 5530249925638308684565818 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32512339312827616756562444023) ^ 921891266986917422989266 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32512339312827616756562444023) ^ 366079607148026263602 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 32512339312827616756562444023) ^ 1215314265154190718 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_130049357251310467026249776041 : Nat.Prime 130049357251310467026249776041 := by
  apply lucas_primality 130049357251310467026249776041 (11 : ZMod 130049357251310467026249776041)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_5
      · exact prime_oneHundredTenDD_107
      · exact prime_oneHundredTenDD_43001837
      · exact prime_oneHundredTenDD_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 130049357251310467026249776041) ^ 65024678625655233513124888020 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 130049357251310467026249776041) ^ 43349785750436822342083258680 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 130049357251310467026249776041) ^ 26009871450262093405249955208 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 130049357251310467026249776041) ^ 1215414553750565112394857720 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 130049357251310467026249776041) ^ 3024274457189130478920 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (11 : ZMod 130049357251310467026249776041) ^ 1656430761240 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_130049357251310467026249776057 : Nat.Prime 130049357251310467026249776057 := by
  apply lucas_primality 130049357251310467026249776057 (3 : ZMod 130049357251310467026249776057)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4015201, 1), (208088557, 1), (19456411085651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4015201, 1), (208088557, 1), (19456411085651, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_4015201
      · exact prime_oneHundredTenDD_208088557
      · exact prime_oneHundredTenDD_19456411085651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130049357251310467026249776057) ^ 65024678625655233513124888028 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 130049357251310467026249776057) ^ 32389252057695359964856 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 130049357251310467026249776057) ^ 624971209980135846808 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (3 : ZMod 130049357251310467026249776057) ^ 6684139057239656 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_130049357251310467026249776059 : Nat.Prime 130049357251310467026249776059 := by
  apply lucas_primality 130049357251310467026249776059 (2 : ZMod 130049357251310467026249776059)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (344045918654260494778438561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (344045918654260494778438561, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_3
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_344045918654260494778438561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 130049357251310467026249776059) ^ 65024678625655233513124888029 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 130049357251310467026249776059) ^ 43349785750436822342083258686 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 130049357251310467026249776059) ^ 18578479607330066718035682294 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (2 : ZMod 130049357251310467026249776059) ^ 378 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem prime_oneHundredTenDD_130049357251310467026249776087 : Nat.Prime 130049357251310467026249776087 := by
  apply lucas_primality 130049357251310467026249776087 (5 : ZMod 130049357251310467026249776087)
  · rw [← oneHundredTenDDFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (83, 1), (199, 1), (15200129274940369969381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (83, 1), (199, 1), (15200129274940369969381, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTenDD_2
      · exact prime_oneHundredTenDD_7
      · exact prime_oneHundredTenDD_37
      · exact prime_oneHundredTenDD_83
      · exact prime_oneHundredTenDD_199
      · exact prime_oneHundredTenDD_15200129274940369969381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 130049357251310467026249776087) ^ 65024678625655233513124888043 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 130049357251310467026249776087) ^ 18578479607330066718035682298 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 130049357251310467026249776087) ^ 3514847493278661270979723678 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 130049357251310467026249776087) ^ 1566859725919403217183732242 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 130049357251310467026249776087) ^ 653514358046786266463566714 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide
    · change (5 : ZMod 130049357251310467026249776087) ^ 8555806 ≠ 1
      rw [← oneHundredTenDDFastPow_eq_pow]
      decide

private theorem phi_oneHundredTenDD_130049357251310467026249776000 : Nat.totient 130049357251310467026249776000 = 47290399383401874189158400000 := by
  rw [← show ((([(2, 7), (5, 3), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_5, prime_oneHundredTenDD_11, prime_oneHundredTenDD_171401, prime_oneHundredTenDD_714027719, prime_oneHundredTenDD_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776001 : Nat.totient 130049357251310467026249776001 = 86379646697158032771819189840 := by
  rw [← show ((([(3, 1), (271, 1), (465329339, 1), (343761494570627743, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_271, prime_oneHundredTenDD_465329339, prime_oneHundredTenDD_343761494570627743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776002 : Nat.totient 130049357251310467026249776002 = 55729926454384705188998638080 := by
  rw [← show ((([(2, 1), (7, 1), (10111, 1), (5121009329, 1), (179403328798297, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_7, prime_oneHundredTenDD_10111, prime_oneHundredTenDD_5121009329, prime_oneHundredTenDD_179403328798297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776003 : Nat.totient 130049357251310467026249776003 = 125319360383321430747748512000 := by
  rw [← show ((([(41, 1), (83, 1), (4261, 1), (8968807997203239919541, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_41, prime_oneHundredTenDD_83, prime_oneHundredTenDD_4261, prime_oneHundredTenDD_8968807997203239919541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776004 : Nat.totient 130049357251310467026249776004 = 41250865408260582582144000000 := by
  rw [← show ((([(2, 2), (3, 4), (31, 1), (61, 1), (3251, 1), (371387, 1), (5760091, 1), (30520993, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_31, prime_oneHundredTenDD_61, prime_oneHundredTenDD_3251, prime_oneHundredTenDD_371387, prime_oneHundredTenDD_5760091, prime_oneHundredTenDD_30520993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776005 : Nat.totient 130049357251310467026249776005 = 104039472983905716134249769408 := by
  rw [← show ((([(5, 1), (8146423, 1), (2267521189, 1), (1408055893883, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_5, prime_oneHundredTenDD_8146423, prime_oneHundredTenDD_2267521189, prime_oneHundredTenDD_1408055893883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776006 : Nat.totient 130049357251310467026249776006 = 61602313910375458624233155040 := by
  rw [← show ((([(2, 1), (19, 1), (4663781, 1), (733814796752556207677, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_19, prime_oneHundredTenDD_4663781, prime_oneHundredTenDD_733814796752556207677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776007 : Nat.totient 130049357251310467026249776007 = 86699568360022062242910052512 := by
  rw [← show ((([(3, 1), (38002823, 1), (100878469, 1), (11307656677487, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_38002823, prime_oneHundredTenDD_100878469, prime_oneHundredTenDD_11307656677487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776008 : Nat.totient 130049357251310467026249776008 = 65021781041829840026492601600 := by
  rw [← show ((([(2, 3), (22441, 1), (724395956348371658049161, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_22441, prime_oneHundredTenDD_724395956348371658049161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776009 : Nat.totient 130049357251310467026249776009 = 111470876360836709960218299264 := by
  rw [← show ((([(7, 1), (93492409, 1), (1236485539, 1), (160710694637, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_7, prime_oneHundredTenDD_93492409, prime_oneHundredTenDD_1236485539, prime_oneHundredTenDD_160710694637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776010 : Nat.totient 130049357251310467026249776010 = 34676349808320250331130224640 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_5, prime_oneHundredTenDD_18541, prime_oneHundredTenDD_21617, prime_oneHundredTenDD_8348687, prime_oneHundredTenDD_1295508299753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776011 : Nat.totient 130049357251310467026249776011 = 109132327763337454847202609120 := by
  rw [← show ((([(11, 1), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_11, prime_oneHundredTenDD_13, prime_oneHundredTenDD_909436064694478790393355077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776012 : Nat.totient 130049357251310467026249776012 = 62983545215881302416300323968 := by
  rw [← show ((([(2, 2), (37, 1), (223, 1), (3940411987980561962981753, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_37, prime_oneHundredTenDD_223, prime_oneHundredTenDD_3940411987980561962981753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776013 : Nat.totient 130049357251310467026249776013 = 86698631189045386670384588616 := by
  rw [← show ((([(3, 2), (92203, 1), (156718638043002296895919, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_92203, prime_oneHundredTenDD_156718638043002296895919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776014 : Nat.totient 130049357251310467026249776014 = 62968496775077084037648804288 := by
  rw [← show ((([(2, 1), (59, 1), (67, 1), (122791657, 1), (133962282976311967, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_59, prime_oneHundredTenDD_67, prime_oneHundredTenDD_122791657, prime_oneHundredTenDD_133962282976311967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776015 : Nat.totient 130049357251310467026249776015 = 99516029896654966072260698080 := by
  rw [← show ((([(5, 1), (23, 1), (1130863976098351887184780661, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_5, prime_oneHundredTenDD_23, prime_oneHundredTenDD_1130863976098351887184780661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776016 : Nat.totient 130049357251310467026249776016 = 34921930605109123254057566208 := by
  rw [← show ((([(2, 4), (3, 1), (7, 1), (17, 1), (709, 1), (95656009, 1), (335707867311353, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_7, prime_oneHundredTenDD_17, prime_oneHundredTenDD_709, prime_oneHundredTenDD_95656009, prime_oneHundredTenDD_335707867311353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776017 : Nat.totient 130049357251310467026249776017 = 129516841695967244831077128000 := by
  rw [← show ((([(269, 1), (4951, 1), (5659, 1), (1063340107, 1), (16227481211, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_269, prime_oneHundredTenDD_4951, prime_oneHundredTenDD_5659, prime_oneHundredTenDD_1063340107, prime_oneHundredTenDD_16227481211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776018 : Nat.totient 130049357251310467026249776018 = 64428121940599217392345890000 := by
  rw [← show ((([(2, 1), (109, 1), (154518491651, 1), (3860746233443951, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_109, prime_oneHundredTenDD_154518491651, prime_oneHundredTenDD_3860746233443951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776019 : Nat.totient 130049357251310467026249776019 = 86699480500726174517934036960 := by
  rw [← show ((([(3, 1), (952741, 1), (45500073735083115287453, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_952741, prime_oneHundredTenDD_45500073735083115287453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776020 : Nat.totient 130049357251310467026249776020 = 51422566509003960098512260480 := by
  rw [← show ((([(2, 2), (5, 1), (167, 1), (181, 1), (215121178501522590773563, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_5, prime_oneHundredTenDD_167, prime_oneHundredTenDD_181, prime_oneHundredTenDD_215121178501522590773563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776021 : Nat.totient 130049357251310467026249776021 = 129667313170311989701433987520 := by
  rw [← show ((([(349, 1), (13781, 1), (27039711302886072957109, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_349, prime_oneHundredTenDD_13781, prime_oneHundredTenDD_27039711302886072957109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776022 : Nat.totient 130049357251310467026249776022 = 39408831235488645766442485440 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_11, prime_oneHundredTenDD_607213, prime_oneHundredTenDD_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776023 : Nat.totient 130049357251310467026249776023 = 111468014497609866817337014944 := by
  rw [← show ((([(7, 1), (38933, 1), (477191061755581812807533, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_7, prime_oneHundredTenDD_38933, prime_oneHundredTenDD_477191061755581812807533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776024 : Nat.totient 130049357251310467026249776024 = 59742577169229639139983360000 := by
  rw [← show ((([(2, 3), (13, 1), (257, 1), (1291, 1), (351257, 1), (353501, 1), (30352877609, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_13, prime_oneHundredTenDD_257, prime_oneHundredTenDD_1291, prime_oneHundredTenDD_351257, prime_oneHundredTenDD_353501, prime_oneHundredTenDD_30352877609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776025 : Nat.totient 130049357251310467026249776025 = 63433064228627496830577131520 := by
  rw [← show ((([(3, 1), (5, 2), (19, 1), (29, 1), (12893, 1), (13873, 1), (83639, 1), (210359508407, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_5, prime_oneHundredTenDD_19, prime_oneHundredTenDD_29, prime_oneHundredTenDD_12893, prime_oneHundredTenDD_13873, prime_oneHundredTenDD_83639, prime_oneHundredTenDD_210359508407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776026 : Nat.totient 130049357251310467026249776026 = 63026533077716856536491857408 := by
  rw [← show ((([(2, 1), (43, 1), (163, 1), (683, 1), (23017, 1), (55373, 1), (10657483763819, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_43, prime_oneHundredTenDD_163, prime_oneHundredTenDD_683, prime_oneHundredTenDD_23017, prime_oneHundredTenDD_55373, prime_oneHundredTenDD_10657483763819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776027 : Nat.totient 130049357251310467026249776027 = 129977546411607376488860177800 := by
  rw [← show ((([(1811, 1), (3204713531, 1), (22407868425741947, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_1811, prime_oneHundredTenDD_3204713531, prime_oneHundredTenDD_22407868425741947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776028 : Nat.totient 130049357251310467026249776028 = 43260771815507562535800181440 := by
  rw [← show ((([(2, 2), (3, 1), (487, 1), (37616242861, 1), (591592401373367, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_487, prime_oneHundredTenDD_37616242861, prime_oneHundredTenDD_591592401373367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776029 : Nat.totient 130049357251310467026249776029 = 127282349650218754961861482876 := by
  rw [← show ((([(47, 1), (2767007601091712064388293107, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_47, prime_oneHundredTenDD_2767007601091712064388293107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776030 : Nat.totient 130049357251310467026249776030 = 44588351049380357748629907744 := by
  rw [← show ((([(2, 1), (5, 1), (7, 3), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_5, prime_oneHundredTenDD_7, prime_oneHundredTenDD_5429792839, prime_oneHundredTenDD_6982819718723939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776031 : Nat.totient 130049357251310467026249776031 = 85857374866741957265260294944 := by
  rw [← show ((([(3, 3), (103, 1), (189439, 1), (246852669850875834709, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_103, prime_oneHundredTenDD_189439, prime_oneHundredTenDD_246852669850875834709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776032 : Nat.totient 130049357251310467026249776032 = 64108061064386282357633228800 := by
  rw [← show ((([(2, 5), (101, 1), (239, 1), (19577, 1), (405749, 1), (21195094540883, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_101, prime_oneHundredTenDD_239, prime_oneHundredTenDD_19577, prime_oneHundredTenDD_405749, prime_oneHundredTenDD_21195094540883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776033 : Nat.totient 130049357251310467026249776033 = 111058603085801376883735603200 := by
  rw [← show ((([(11, 1), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_11, prime_oneHundredTenDD_17, prime_oneHundredTenDD_521, prime_oneHundredTenDD_23096547757, prime_oneHundredTenDD_57793874370247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776034 : Nat.totient 130049357251310467026249776034 = 43349785748520631168508136480 := by
  rw [← show ((([(2, 1), (3, 1), (22622892419, 1), (958095564164668681, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_22622892419, prime_oneHundredTenDD_958095564164668681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776035 : Nat.totient 130049357251310467026249776035 = 100683373324996626726126157920 := by
  rw [← show ((([(5, 1), (31, 1), (3262940519, 1), (257138647306974463, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_5, prime_oneHundredTenDD_31, prime_oneHundredTenDD_3262940519, prime_oneHundredTenDD_257138647306974463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776036 : Nat.totient 130049357251310467026249776036 = 64281018608631894271447872000 := by
  rw [← show ((([(2, 2), (89, 1), (4931, 1), (9312211, 1), (7955553520153241, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_89, prime_oneHundredTenDD_4931, prime_oneHundredTenDD_9312211, prime_oneHundredTenDD_7955553520153241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776037 : Nat.totient 130049357251310467026249776037 = 68594826898960994862630017280 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (26021, 1), (2153283367, 1), (8501986179367, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_7, prime_oneHundredTenDD_13, prime_oneHundredTenDD_26021, prime_oneHundredTenDD_2153283367, prime_oneHundredTenDD_8501986179367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776038 : Nat.totient 130049357251310467026249776038 = 62075088822701382314789485440 := by
  rw [← show ((([(2, 1), (23, 2), (509, 1), (264889, 1), (911676659536508311, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_23, prime_oneHundredTenDD_509, prime_oneHundredTenDD_264889, prime_oneHundredTenDD_911676659536508311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776039 : Nat.totient 130049357251310467026249776039 = 130046674333060145623643340192 := by
  rw [← show ((([(55927, 1), (366853, 1), (42187207, 1), (150249777467, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_55927, prime_oneHundredTenDD_366853, prime_oneHundredTenDD_42187207, prime_oneHundredTenDD_150249777467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776040 : Nat.totient 130049357251310467026249776040 = 34355717253746584092593118720 := by
  rw [← show ((([(2, 3), (3, 2), (5, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_5, prime_oneHundredTenDD_107, prime_oneHundredTenDD_43001837, prime_oneHundredTenDD_78511797954027271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776041 : Nat.totient 130049357251310467026249776041 = 130049357251310467026249776040 := by
  rw [← show ((([(130049357251310467026249776041, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_130049357251310467026249776041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776042 : Nat.totient 130049357251310467026249776042 = 64873712572279284777308967360 := by
  rw [← show ((([(2, 1), (431, 1), (670673, 1), (224952136074415902667, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_431, prime_oneHundredTenDD_670673, prime_oneHundredTenDD_224952136074415902667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776043 : Nat.totient 130049357251310467026249776043 = 86699211030713506877630916480 := by
  rw [← show ((([(3, 1), (316271, 1), (1004167, 1), (136496538697859633, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_316271, prime_oneHundredTenDD_1004167, prime_oneHundredTenDD_136496538697859633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776044 : Nat.totient 130049357251310467026249776044 = 46713071663293406800497868800 := by
  rw [← show ((([(2, 2), (7, 1), (11, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_7, prime_oneHundredTenDD_11, prime_oneHundredTenDD_19, prime_oneHundredTenDD_41, prime_oneHundredTenDD_397, prime_oneHundredTenDD_13617913, prime_oneHundredTenDD_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776045 : Nat.totient 130049357251310467026249776045 = 104013611768110491706093171200 := by
  rw [← show ((([(5, 1), (4021, 1), (700722673081, 1), (9231195796909, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_5, prime_oneHundredTenDD_4021, prime_oneHundredTenDD_700722673081, prime_oneHundredTenDD_9231195796909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776046 : Nat.totient 130049357251310467026249776046 = 43349768359748669034953856000 := by
  rw [← show ((([(2, 1), (3, 1), (2492701, 1), (8695344076653562208641, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_2492701, prime_oneHundredTenDD_8695344076653562208641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776047 : Nat.totient 130049357251310467026249776047 = 127595324505957799631392276128 := by
  rw [← show ((([(53, 1), (470333, 1), (5217072707149818541903, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_53, prime_oneHundredTenDD_470333, prime_oneHundredTenDD_5217072707149818541903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776048 : Nat.totient 130049357251310467026249776048 = 65024638618371364261909499520 := by
  rw [← show ((([(2, 4), (1625321, 1), (5000910483656400298243, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_1625321, prime_oneHundredTenDD_5000910483656400298243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776049 : Nat.totient 130049357251310467026249776049 = 83192720363929515231830246400 := by
  rw [← show ((([(3, 2), (37, 1), (139, 1), (157, 1), (3571, 1), (5011406982273367241, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_37, prime_oneHundredTenDD_139, prime_oneHundredTenDD_157, prime_oneHundredTenDD_3571, prime_oneHundredTenDD_5011406982273367241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776050 : Nat.totient 130049357251310467026249776050 = 45187669211799330688196736000 := by
  rw [← show ((([(2, 1), (5, 2), (13, 1), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_5, prime_oneHundredTenDD_13, prime_oneHundredTenDD_17, prime_oneHundredTenDD_7591, prime_oneHundredTenDD_1550411355806685423811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776051 : Nat.totient 130049357251310467026249776051 = 111448298142146967170325629760 := by
  rw [← show ((([(7, 1), (6217, 1), (23971, 1), (124664600840500529999, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_7, prime_oneHundredTenDD_6217, prime_oneHundredTenDD_23971, prime_oneHundredTenDD_124664600840500529999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776052 : Nat.totient 130049357251310467026249776052 = 43349763879845726153057356800 := by
  rw [← show ((([(2, 2), (3, 1), (3148051, 1), (5351669, 1), (643273943197409, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_3148051, prime_oneHundredTenDD_5351669, prime_oneHundredTenDD_643273943197409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776053 : Nat.totient 130049357251310467026249776053 = 126545362030294459974763776000 := by
  rw [← show ((([(71, 1), (137, 1), (173, 1), (184631, 1), (376010941, 1), (1113212533, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_71, prime_oneHundredTenDD_137, prime_oneHundredTenDD_173, prime_oneHundredTenDD_184631, prime_oneHundredTenDD_376010941, prime_oneHundredTenDD_1113212533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776054 : Nat.totient 130049357251310467026249776054 = 62366670524720708096625830400 := by
  rw [← show ((([(2, 1), (29, 1), (151, 1), (14849207267790644784910913, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_29, prime_oneHundredTenDD_151, prime_oneHundredTenDD_14849207267790644784910913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776055 : Nat.totient 130049357251310467026249776055 = 62916557879616814410039552000 := by
  rw [← show ((([(3, 1), (5, 1), (11, 2), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_5, prime_oneHundredTenDD_11, prime_oneHundredTenDD_461, prime_oneHundredTenDD_69997, prime_oneHundredTenDD_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776056 : Nat.totient 130049357251310467026249776056 = 65024662118540335432341120000 := by
  rw [← show ((([(2, 3), (4015201, 1), (208088557, 1), (19456411085651, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_4015201, prime_oneHundredTenDD_208088557, prime_oneHundredTenDD_19456411085651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776057 : Nat.totient 130049357251310467026249776057 = 130049357251310467026249776056 := by
  rw [← show ((([(130049357251310467026249776057, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_130049357251310467026249776057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776058 : Nat.totient 130049357251310467026249776058 = 37156959214660133436071364480 := by
  rw [← show ((([(2, 1), (3, 3), (7, 1), (344045918654260494778438561, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_7, prime_oneHundredTenDD_344045918654260494778438561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776059 : Nat.totient 130049357251310467026249776059 = 130049357251310467026249776058 := by
  rw [← show ((([(130049357251310467026249776059, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_130049357251310467026249776059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776060 : Nat.totient 130049357251310467026249776060 = 52019742900524186810499910416 := by
  rw [← show ((([(2, 2), (5, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_5, prime_oneHundredTenDD_6502467862565523351312488803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776061 : Nat.totient 130049357251310467026249776061 = 82896393092768049169909195200 := by
  rw [← show ((([(3, 1), (23, 1), (2467, 1), (5154157, 1), (148228709119623551, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_23, prime_oneHundredTenDD_2467, prime_oneHundredTenDD_5154157, prime_oneHundredTenDD_148228709119623551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776062 : Nat.totient 130049357251310467026249776062 = 64817662094186830425406244160 := by
  rw [← show ((([(2, 1), (571, 1), (857, 1), (3727, 1), (35653477162396384699, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_571, prime_oneHundredTenDD_857, prime_oneHundredTenDD_3727, prime_oneHundredTenDD_35653477162396384699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776063 : Nat.totient 130049357251310467026249776063 = 113723781789919288608243909216 := by
  rw [← show ((([(13, 1), (19, 1), (31667, 1), (16626633921813454641187, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_13, prime_oneHundredTenDD_19, prime_oneHundredTenDD_31667, prime_oneHundredTenDD_16626633921813454641187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776064 : Nat.totient 130049357251310467026249776064 = 43349768019730666203443215104 := by
  rw [← show ((([(2, 6), (3, 1), (2444899, 1), (277042283689663805783, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_2444899, prime_oneHundredTenDD_277042283689663805783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776065 : Nat.totient 130049357251310467026249776065 = 87714550426224057369221744640 := by
  rw [← show ((([(5, 1), (7, 1), (61, 1), (368873, 1), (117238469, 1), (1408520993987, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_5, prime_oneHundredTenDD_7, prime_oneHundredTenDD_61, prime_oneHundredTenDD_368873, prime_oneHundredTenDD_117238469, prime_oneHundredTenDD_1408520993987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776066 : Nat.totient 130049357251310467026249776066 = 57206446238948054048720294400 := by
  rw [← show ((([(2, 1), (11, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_11, prime_oneHundredTenDD_31, prime_oneHundredTenDD_3599009, prime_oneHundredTenDD_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776067 : Nat.totient 130049357251310467026249776067 = 80619177817363387048520712192 := by
  rw [← show ((([(3, 2), (17, 1), (97, 1), (773, 1), (2333, 1), (571397, 1), (8503796454319, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_17, prime_oneHundredTenDD_97, prime_oneHundredTenDD_773, prime_oneHundredTenDD_2333, prime_oneHundredTenDD_571397, prime_oneHundredTenDD_8503796454319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776068 : Nat.totient 130049357251310467026249776068 = 65024321200814755353872538240 := by
  rw [← show ((([(2, 2), (183569, 1), (20319371, 1), (8716429397529283, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_183569, prime_oneHundredTenDD_20319371, prime_oneHundredTenDD_8716429397529283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776069 : Nat.totient 130049357251310467026249776069 = 125284885736847038001713702880 := by
  rw [← show ((([(43, 1), (73, 1), (41430187082290687169878871, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_43, prime_oneHundredTenDD_73, prime_oneHundredTenDD_41430187082290687169878871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776070 : Nat.totient 130049357251310467026249776070 = 34240842736059346995881040768 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (79, 1), (49471423, 1), (1109188763774599357, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_5, prime_oneHundredTenDD_79, prime_oneHundredTenDD_49471423, prime_oneHundredTenDD_1109188763774599357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776071 : Nat.totient 130049357251310467026249776071 = 129939542399985624454566600000 := by
  rw [← show ((([(1307, 1), (12601, 1), (62053524251, 1), (127250986903, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_1307, prime_oneHundredTenDD_12601, prime_oneHundredTenDD_62053524251, prime_oneHundredTenDD_127250986903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776072 : Nat.totient 130049357251310467026249776072 = 55735438821990200154107046864 := by
  rw [← show ((([(2, 3), (7, 1), (2322309950916258339754460287, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_7, prime_oneHundredTenDD_2322309950916258339754460287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776073 : Nat.totient 130049357251310467026249776073 = 84579475296854203486687651200 := by
  rw [← show ((([(3, 1), (59, 1), (131, 1), (143762009, 1), (39013913335236331, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_59, prime_oneHundredTenDD_131, prime_oneHundredTenDD_143762009, prime_oneHundredTenDD_39013913335236331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776074 : Nat.totient 130049357251310467026249776074 = 65020529132109041148156567744 := by
  rw [← show ((([(2, 1), (15679, 1), (28936619, 1), (143321738727393937, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_15679, prime_oneHundredTenDD_28936619, prime_oneHundredTenDD_143321738727393937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776075 : Nat.totient 130049357251310467026249776075 = 103771989822290364584084544000 := by
  rw [← show ((([(5, 2), (389, 1), (4186181, 1), (5930381, 1), (538664062567, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_5, prime_oneHundredTenDD_389, prime_oneHundredTenDD_4186181, prime_oneHundredTenDD_5930381, prime_oneHundredTenDD_538664062567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776076 : Nat.totient 130049357251310467026249776076 = 39163786358574749319845941248 := by
  rw [← show ((([(2, 2), (3, 2), (13, 1), (47, 1), (2893777, 1), (2043146173337516953, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_13, prime_oneHundredTenDD_47, prime_oneHundredTenDD_2893777, prime_oneHundredTenDD_2043146173337516953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776077 : Nat.totient 130049357251310467026249776077 = 118158071643938492174960207760 := by
  rw [← show ((([(11, 1), (1723, 1), (6861676634375057617593509, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_11, prime_oneHundredTenDD_1723, prime_oneHundredTenDD_6861676634375057617593509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776078 : Nat.totient 130049357251310467026249776078 = 64870224214966678244760861600 := by
  rw [← show ((([(2, 1), (421, 1), (43468861, 1), (3553185310071156919, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_421, prime_oneHundredTenDD_43468861, prime_oneHundredTenDD_3553185310071156919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776079 : Nat.totient 130049357251310467026249776079 = 74093262099247967296692658176 := by
  rw [← show ((([(3, 1), (7, 2), (337, 1), (528289, 1), (4969233525257565349, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_7, prime_oneHundredTenDD_337, prime_oneHundredTenDD_528289, prime_oneHundredTenDD_4969233525257565349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776080 : Nat.totient 130049357251310467026249776080 = 52019742900524186810499910400 := by
  rw [← show ((([(2, 4), (5, 1), (1625616965641380837828122201, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_5, prime_oneHundredTenDD_1625616965641380837828122201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776081 : Nat.totient 130049357251310467026249776081 = 128050641596975532253402858560 := by
  rw [← show ((([(67, 1), (2221, 1), (56101637827, 1), (15577914241229, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_67, prime_oneHundredTenDD_2221, prime_oneHundredTenDD_56101637827, prime_oneHundredTenDD_15577914241229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776082 : Nat.totient 130049357251310467026249776082 = 41068206955981647987358928400 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (3692063, 1), (308982765336835019951, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_19, prime_oneHundredTenDD_3692063, prime_oneHundredTenDD_308982765336835019951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776083 : Nat.totient 130049357251310467026249776083 = 125564896656437692301206680328 := by
  rw [← show ((([(29, 1), (4484460594872774725043095727, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_29, prime_oneHundredTenDD_4484460594872774725043095727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776084 : Nat.totient 130049357251310467026249776084 = 58538841093907316164660796928 := by
  rw [← show ((([(2, 2), (17, 1), (23, 1), (2688712237, 1), (30926241121730063, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_17, prime_oneHundredTenDD_23, prime_oneHundredTenDD_2688712237, prime_oneHundredTenDD_30926241121730063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776085 : Nat.totient 130049357251310467026249776085 = 67667958080732937003894316800 := by
  rw [← show ((([(3, 4), (5, 1), (41, 1), (412983787, 1), (18964278642836171, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_5, prime_oneHundredTenDD_41, prime_oneHundredTenDD_412983787, prime_oneHundredTenDD_18964278642836171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776086 : Nat.totient 130049357251310467026249776086 = 53306488564113278913736394880 := by
  rw [← show ((([(2, 1), (7, 1), (37, 1), (83, 1), (199, 1), (15200129274940369969381, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_7, prime_oneHundredTenDD_37, prime_oneHundredTenDD_83, prime_oneHundredTenDD_199, prime_oneHundredTenDD_15200129274940369969381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776087 : Nat.totient 130049357251310467026249776087 = 130049357251310467026249776086 := by
  rw [← show ((([(130049357251310467026249776087, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_130049357251310467026249776087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776088 : Nat.totient 130049357251310467026249776088 = 39401075104513765330990579200 := by
  rw [← show ((([(2, 3), (3, 1), (11, 1), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_11, prime_oneHundredTenDD_5879, prime_oneHundredTenDD_35267, prime_oneHundredTenDD_88812211, prime_oneHundredTenDD_26752207429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776089 : Nat.totient 130049357251310467026249776089 = 120045560539671200331922870224 := by
  rw [← show ((([(13, 1), (10003796711639266694326905853, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_13, prime_oneHundredTenDD_10003796711639266694326905853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776090 : Nat.totient 130049357251310467026249776090 = 51985925303636389622193616896 := by
  rw [← show ((([(2, 1), (5, 1), (1579, 1), (70729, 1), (377137, 1), (308765963399027, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_5, prime_oneHundredTenDD_1579, prime_oneHundredTenDD_70729, prime_oneHundredTenDD_377137, prime_oneHundredTenDD_308765963399027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776091 : Nat.totient 130049357251310467026249776091 = 86699312887306715463574136960 := by
  rw [← show ((([(3, 1), (335249, 1), (83162934731, 1), (1554854151563, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_335249, prime_oneHundredTenDD_83162934731, prime_oneHundredTenDD_1554854151563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776092 : Nat.totient 130049357251310467026249776092 = 65024678625655233513124888044 := by
  rw [← show ((([(2, 2), (32512339312827616756562444023, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_32512339312827616756562444023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776093 : Nat.totient 130049357251310467026249776093 = 111249265492609904526342036720 := by
  rw [← show ((([(7, 1), (503, 1), (1622199443, 1), (22768684387884431, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_7, prime_oneHundredTenDD_503, prime_oneHundredTenDD_1622199443, prime_oneHundredTenDD_22768684387884431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776094 : Nat.totient 130049357251310467026249776094 = 43344158100722368645816552320 := by
  rw [← show ((([(2, 1), (3, 2), (7703, 1), (937941619075616044443361, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_7703, prime_oneHundredTenDD_937941619075616044443361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776095 : Nat.totient 130049357251310467026249776095 = 104039485801048373620999820872 := by
  rw [← show ((([(5, 1), (26009871450262093405249955219, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_5, prime_oneHundredTenDD_26009871450262093405249955219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776096 : Nat.totient 130049357251310467026249776096 = 65024678427287506033326471808 := by
  rw [← show ((([(2, 5), (327798677, 1), (12397982967159602339, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_327798677, prime_oneHundredTenDD_12397982967159602339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776097 : Nat.totient 130049357251310467026249776097 = 83902811129877720662096629680 := by
  rw [← show ((([(3, 1), (31, 1), (1398380185497962011034943829, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_3, prime_oneHundredTenDD_31, prime_oneHundredTenDD_1398380185497962011034943829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776098 : Nat.totient 130049357251310467026249776098 = 64643647646188064238476245200 := by
  rw [← show ((([(2, 1), (307, 1), (383, 1), (427597171451, 1), (1293320737679, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_307, prime_oneHundredTenDD_383, prime_oneHundredTenDD_427597171451, prime_oneHundredTenDD_1293320737679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776099 : Nat.totient 130049357251310467026249776099 = 117174941096034291085040695200 := by
  rw [← show ((([(11, 1), (127, 1), (971, 1), (3962759, 1), (24193288987440403, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_11, prime_oneHundredTenDD_127, prime_oneHundredTenDD_971, prime_oneHundredTenDD_3962759, prime_oneHundredTenDD_24193288987440403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776100 : Nat.totient 130049357251310467026249776100 = 29146143187584913286494963200 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (7, 1), (53, 1), (1571, 1), (743766923576701404707, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_2, prime_oneHundredTenDD_3, prime_oneHundredTenDD_5, prime_oneHundredTenDD_7, prime_oneHundredTenDD_53, prime_oneHundredTenDD_1571, prime_oneHundredTenDD_743766923576701404707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTenDD_130049357251310467026249776101 : Nat.totient 130049357251310467026249776101 = 115957321633819166893817372928 := by
  rw [← show ((([(17, 1), (19, 1), (57285360053, 1), (7028490152472379, 1)] : List FactorBlock).map factorBlockValue).prod) = 130049357251310467026249776101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTenDD_17, prime_oneHundredTenDD_19, prime_oneHundredTenDD_57285360053, prime_oneHundredTenDD_7028490152472379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTenDD : certifiedKill 1 130049357251310467026249775999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTenDD_130049357251310467026249776000, phi_oneHundredTenDD_130049357251310467026249776001, phi_oneHundredTenDD_130049357251310467026249776002,
    phi_oneHundredTenDD_130049357251310467026249776003, phi_oneHundredTenDD_130049357251310467026249776004, phi_oneHundredTenDD_130049357251310467026249776005,
    phi_oneHundredTenDD_130049357251310467026249776006, phi_oneHundredTenDD_130049357251310467026249776007, phi_oneHundredTenDD_130049357251310467026249776008,
    phi_oneHundredTenDD_130049357251310467026249776009, phi_oneHundredTenDD_130049357251310467026249776010, phi_oneHundredTenDD_130049357251310467026249776011,
    phi_oneHundredTenDD_130049357251310467026249776012, phi_oneHundredTenDD_130049357251310467026249776013, phi_oneHundredTenDD_130049357251310467026249776014,
    phi_oneHundredTenDD_130049357251310467026249776015, phi_oneHundredTenDD_130049357251310467026249776016, phi_oneHundredTenDD_130049357251310467026249776017,
    phi_oneHundredTenDD_130049357251310467026249776018, phi_oneHundredTenDD_130049357251310467026249776019, phi_oneHundredTenDD_130049357251310467026249776020,
    phi_oneHundredTenDD_130049357251310467026249776021, phi_oneHundredTenDD_130049357251310467026249776022, phi_oneHundredTenDD_130049357251310467026249776023,
    phi_oneHundredTenDD_130049357251310467026249776024, phi_oneHundredTenDD_130049357251310467026249776025, phi_oneHundredTenDD_130049357251310467026249776026,
    phi_oneHundredTenDD_130049357251310467026249776027, phi_oneHundredTenDD_130049357251310467026249776028, phi_oneHundredTenDD_130049357251310467026249776029,
    phi_oneHundredTenDD_130049357251310467026249776030, phi_oneHundredTenDD_130049357251310467026249776031, phi_oneHundredTenDD_130049357251310467026249776032,
    phi_oneHundredTenDD_130049357251310467026249776033, phi_oneHundredTenDD_130049357251310467026249776034, phi_oneHundredTenDD_130049357251310467026249776035,
    phi_oneHundredTenDD_130049357251310467026249776036, phi_oneHundredTenDD_130049357251310467026249776037, phi_oneHundredTenDD_130049357251310467026249776038,
    phi_oneHundredTenDD_130049357251310467026249776039, phi_oneHundredTenDD_130049357251310467026249776040, phi_oneHundredTenDD_130049357251310467026249776041,
    phi_oneHundredTenDD_130049357251310467026249776042, phi_oneHundredTenDD_130049357251310467026249776043, phi_oneHundredTenDD_130049357251310467026249776044,
    phi_oneHundredTenDD_130049357251310467026249776045, phi_oneHundredTenDD_130049357251310467026249776046, phi_oneHundredTenDD_130049357251310467026249776047,
    phi_oneHundredTenDD_130049357251310467026249776048, phi_oneHundredTenDD_130049357251310467026249776049, phi_oneHundredTenDD_130049357251310467026249776050,
    phi_oneHundredTenDD_130049357251310467026249776051, phi_oneHundredTenDD_130049357251310467026249776052, phi_oneHundredTenDD_130049357251310467026249776053,
    phi_oneHundredTenDD_130049357251310467026249776054, phi_oneHundredTenDD_130049357251310467026249776055, phi_oneHundredTenDD_130049357251310467026249776056,
    phi_oneHundredTenDD_130049357251310467026249776057, phi_oneHundredTenDD_130049357251310467026249776058, phi_oneHundredTenDD_130049357251310467026249776059,
    phi_oneHundredTenDD_130049357251310467026249776060, phi_oneHundredTenDD_130049357251310467026249776061, phi_oneHundredTenDD_130049357251310467026249776062,
    phi_oneHundredTenDD_130049357251310467026249776063, phi_oneHundredTenDD_130049357251310467026249776064, phi_oneHundredTenDD_130049357251310467026249776065,
    phi_oneHundredTenDD_130049357251310467026249776066, phi_oneHundredTenDD_130049357251310467026249776067, phi_oneHundredTenDD_130049357251310467026249776068,
    phi_oneHundredTenDD_130049357251310467026249776069, phi_oneHundredTenDD_130049357251310467026249776070, phi_oneHundredTenDD_130049357251310467026249776071,
    phi_oneHundredTenDD_130049357251310467026249776072, phi_oneHundredTenDD_130049357251310467026249776073, phi_oneHundredTenDD_130049357251310467026249776074,
    phi_oneHundredTenDD_130049357251310467026249776075, phi_oneHundredTenDD_130049357251310467026249776076, phi_oneHundredTenDD_130049357251310467026249776077,
    phi_oneHundredTenDD_130049357251310467026249776078, phi_oneHundredTenDD_130049357251310467026249776079, phi_oneHundredTenDD_130049357251310467026249776080,
    phi_oneHundredTenDD_130049357251310467026249776081, phi_oneHundredTenDD_130049357251310467026249776082, phi_oneHundredTenDD_130049357251310467026249776083,
    phi_oneHundredTenDD_130049357251310467026249776084, phi_oneHundredTenDD_130049357251310467026249776085, phi_oneHundredTenDD_130049357251310467026249776086,
    phi_oneHundredTenDD_130049357251310467026249776087, phi_oneHundredTenDD_130049357251310467026249776088, phi_oneHundredTenDD_130049357251310467026249776089,
    phi_oneHundredTenDD_130049357251310467026249776090, phi_oneHundredTenDD_130049357251310467026249776091, phi_oneHundredTenDD_130049357251310467026249776092,
    phi_oneHundredTenDD_130049357251310467026249776093, phi_oneHundredTenDD_130049357251310467026249776094, phi_oneHundredTenDD_130049357251310467026249776095,
    phi_oneHundredTenDD_130049357251310467026249776096, phi_oneHundredTenDD_130049357251310467026249776097, phi_oneHundredTenDD_130049357251310467026249776098,
    phi_oneHundredTenDD_130049357251310467026249776099, phi_oneHundredTenDD_130049357251310467026249776100, phi_oneHundredTenDD_130049357251310467026249776101]

end TotientTailPeriodKiller
end Erdos249257
